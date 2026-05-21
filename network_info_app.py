import sys
import subprocess
import socket
import threading
import re
import json
import os
import warnings
import struct
import uuid
import gzip
import time
import sqlite3
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from PyQt5.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
                             QPushButton, QTreeWidget, QTreeWidgetItem, QLabel, QLineEdit,
                             QProgressBar, QMenuBar, QMenu, QToolBar, QTabWidget, QStatusBar,
                             QFrame, QToolButton, QStyle, QHeaderView, QAbstractItemView,
                             QWidgetAction, QCheckBox, QDialog, QFormLayout, QSpinBox,
                             QDoubleSpinBox, QDialogButtonBox, QInputDialog)
from PyQt5.QtCore import Qt, pyqtSignal, QObject
from PyQt5.QtGui import QIcon, QColor, QFont
from ipaddress import IPv4Network


warnings.filterwarnings(
    "ignore",
    message=r"sipPyTypeDict\(\) is deprecated",
    category=DeprecationWarning
)


class ResourceScanner(QObject):
    """Scanner for printers and file shares on discovered devices"""
    found_resource = pyqtSignal(str, str)  # (ip, resource_info)
    
    def find_printers(self, ip):
        """Find printers on a device"""
        try:
            output = subprocess.check_output(
                f'net view \\\\{ip}',
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=2
            )
            for line in output.split('\n'):
                line = line.strip()
                if 'print' in line.lower() or 'printer' in line.lower():
                    return line
        except:
            pass
        return None
    
    def find_shares(self, ip):
        """Find shared folders and files on a device"""
        shares = []
        try:
            output = subprocess.check_output(
                f'net view \\\\{ip}',
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=2
            )
            
            in_shares_section = False
            for line in output.split('\n'):
                line = line.strip()
                
                if '---' in line:
                    in_shares_section = True
                    continue
                
                if in_shares_section and line and not line.startswith('The command'):
                    parts = line.split()
                    if parts:
                        share_name = parts[0]
                        if share_name and not share_name.startswith('C$'):
                            shares.append(share_name)
        except:
            pass
        
        return shares


class NetworkScanner(QObject):
    """Network scanner that runs in a separate thread"""
    HOSTNAME_METHOD_COUNT = 13
    MANUFACTURER_METHOD_COUNT = 3
    update_progress = pyqtSignal(str)
    add_device = pyqtSignal(dict)
    add_resource = pyqtSignal(str, str, str)  # ip, resource_type, resource_name
    scan_complete = pyqtSignal()
    status_update = pyqtSignal(int, int, int)  # alive, dead, unknown
    progress_update = pyqtSignal(int, int)  # current, total
    
    def __init__(self):
        super().__init__()
        self.devices = {}
        self.max_workers = min(128, max(48, (os.cpu_count() or 4) * 12))
        self.detail_workers = min(32, max(8, (os.cpu_count() or 4) * 4))
        self.resource_workers = 12
        self.ping_timeout_ms = 220
        self.process_timeout_sec = 0.9
        self.resource_scanner = ResourceScanner()
        self.detail_executor = ThreadPoolExecutor(max_workers=self.detail_workers)
        self.resource_executor = ThreadPoolExecutor(max_workers=self.resource_workers)
        self.storage_db_path = os.path.join(os.path.dirname(__file__), 'app_storage.db')
        self.vendor_registry_max_age_sec = 30 * 24 * 60 * 60
        self.vendor_cache = {}
        self.vendor_cache_lock = threading.Lock()
        self.vendor_registry = {}
        self.vendor_registry_lock = threading.Lock()
        self.vendor_registry_loaded = False
        self.mdns_service_cache = {}
        self.mdns_cache_lock = threading.Lock()
        self.mdns_cache_populated = False
        self.ssdp_name_cache = {}
        self.ssdp_cache_lock = threading.Lock()
        self.ssdp_cache_populated = False
        self.wsd_name_cache = {}
        self.wsd_cache_lock = threading.Lock()
        self.wsd_cache_populated = False
        self.snmp_name_cache = {}
        self.snmp_cache_lock = threading.Lock()
        self.hostname_cache = {}
        self.hostname_cache_lock = threading.Lock()
        self.local_interface_mac_cache = None
        self.local_interface_mac_lock = threading.Lock()
        self.executor_settings_lock = threading.Lock()
        self.alive_count = 0
        self.dead_count = 0
        self.total_ips = 0
        self.scanned_count = 0
        self._ensure_storage_db()

    def _db_connect(self):
        """Create a short-lived SQLite connection for local storage."""
        return sqlite3.connect(self.storage_db_path, timeout=5)

    def _ensure_storage_db(self):
        """Create the local storage tables if they do not exist yet."""
        try:
            with self._db_connect() as conn:
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS app_cache (
                        cache_key TEXT PRIMARY KEY,
                        payload TEXT NOT NULL,
                        updated_at REAL NOT NULL
                    )
                """)
        except Exception:
            pass

    def apply_runtime_settings(self, max_workers=None, detail_workers=None, resource_workers=None,
                               ping_timeout_ms=None, process_timeout_sec=None):
        """Apply scanner settings without requiring an app restart."""
        with self.executor_settings_lock:
            if max_workers is not None:
                self.max_workers = max(16, int(max_workers))
            if ping_timeout_ms is not None:
                self.ping_timeout_ms = max(50, int(ping_timeout_ms))
            if process_timeout_sec is not None:
                self.process_timeout_sec = max(0.1, float(process_timeout_sec))

            if detail_workers is not None:
                detail_workers = max(4, int(detail_workers))
                if detail_workers != self.detail_workers:
                    old_executor = self.detail_executor
                    self.detail_workers = detail_workers
                    self.detail_executor = ThreadPoolExecutor(max_workers=self.detail_workers)
                    old_executor.shutdown(wait=False, cancel_futures=False)

            if resource_workers is not None:
                resource_workers = max(2, int(resource_workers))
                if resource_workers != self.resource_workers:
                    old_executor = self.resource_executor
                    self.resource_workers = resource_workers
                    self.resource_executor = ThreadPoolExecutor(max_workers=self.resource_workers)
                    old_executor.shutdown(wait=False, cancel_futures=False)
    
    def parse_ip_range(self, range_str):
        """Parse IP range string like 192.168.0.90-110 or 192.168.0.1/24"""
        ips = []
        try:
            if '-' in range_str:
                # Handle 192.168.0.90-110 format
                base_part, end_part = range_str.rsplit('.', 1)
                start_end = end_part.split('-')
                start_ip = int(start_end[0])
                end_ip = int(start_end[1])
                
                for i in range(start_ip, end_ip + 1):
                    ips.append(f"{base_part}.{i}")
            elif '/' in range_str:
                # Handle CIDR notation
                network = IPv4Network(range_str, strict=False)
                ips = [str(ip) for ip in network.hosts()]
            else:
                # Single IP
                ips = [range_str]
        except Exception as e:
            self.update_progress.emit(f"Error parsing IP range: {str(e)}")
        
        return ips
    
    def scan_ips(self, ip_list):
        """Scan multiple IPs in parallel"""
        self.total_ips = len(ip_list)
        self.scanned_count = 0
        self.alive_count = 0
        self.dead_count = 0
        with self.mdns_cache_lock:
            self.mdns_service_cache = {}
            self.mdns_cache_populated = False
        with self.ssdp_cache_lock:
            self.ssdp_name_cache = {}
            self.ssdp_cache_populated = False
        with self.wsd_cache_lock:
            self.wsd_name_cache = {}
            self.wsd_cache_populated = False
        with self.snmp_cache_lock:
            self.snmp_name_cache = {}
        with self.hostname_cache_lock:
            self.hostname_cache = {}

        # Prime non-Windows name discovery once per scan instead of lazily from many workers.
        mdns_prefetch_thread = threading.Thread(target=self._discover_mdns_service_names_cached, daemon=True)
        mdns_prefetch_thread.start()
        ssdp_prefetch_thread = threading.Thread(target=self._discover_ssdp_names_cached, daemon=True)
        ssdp_prefetch_thread.start()
        wsd_prefetch_thread = threading.Thread(target=self._discover_wsd_names_cached, daemon=True)
        wsd_prefetch_thread.start()
        
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = {}
            
            for ip in ip_list:
                future = executor.submit(self._scan_single_ip, ip)
                futures[future] = ip
            
            for future in as_completed(futures):
                self.scanned_count += 1
                self.progress_update.emit(self.scanned_count, self.total_ips)
                
                try:
                    ip, is_alive = future.result()
                    if is_alive:
                        self.alive_count += 1
                        self.add_device.emit({
                            'ip': ip,
                            'name': self._make_loading_marker('name', 1, self.HOSTNAME_METHOD_COUNT),
                            'mac': '',
                            'manufacturer': self._make_loading_marker(
                                'manufacturer', 1, self.MANUFACTURER_METHOD_COUNT
                            ),
                            'status': 'Online',
                        })
                        self.update_progress.emit(f"Found: {ip}")
                        self.detail_executor.submit(self._collect_and_emit_details, ip)
                    else:
                        self.dead_count += 1
                except Exception as e:
                    self.dead_count += 1
    
    def _scan_single_ip(self, ip):
        """Scan a single IP address"""
        is_alive = False
        
        try:
            # Check if IP is reachable
            result = subprocess.run(
                ['ping', '-n', '1', '-w', str(self.ping_timeout_ms), ip],
                capture_output=True,
                timeout=self.process_timeout_sec
            )
            
            if result.returncode == 0:
                is_alive = True
        except Exception:
            pass
        
        return ip, is_alive

    def _make_loading_marker(self, marker_type, current_method, total_methods):
        """Create a machine-readable loading marker for UI formatting."""
        return f'__{marker_type.upper()}_LOADING__:{int(current_method)}:{int(total_methods)}'

    def _collect_and_emit_details(self, ip):
        """Gather slower details after the device is already marked alive."""
        try:
            device_state = {
                'ip': ip,
                'name': self._make_loading_marker('name', 1, self.HOSTNAME_METHOD_COUNT),
                'mac': '',
                'manufacturer': self._make_loading_marker(
                    'manufacturer', 1, self.MANUFACTURER_METHOD_COUNT
                ),
                'status': 'Online',
            }

            def emit_state():
                self.add_device.emit(device_state.copy())

            def on_name_progress(current_method, total_methods):
                device_state['name'] = self._make_loading_marker('name', current_method, total_methods)
                emit_state()

            def on_manufacturer_progress(current_method, total_methods):
                device_state['manufacturer'] = self._make_loading_marker(
                    'manufacturer', current_method, total_methods
                )
                emit_state()

            emit_state()
            name = self._get_hostname(ip, progress_callback=on_name_progress)
            device_state['name'] = name
            emit_state()

            mac = self._get_mac_from_arp(ip)
            device_state['mac'] = mac

            manufacturer = self._get_manufacturer_from_mac(mac, progress_callback=on_manufacturer_progress)
            device_state['manufacturer'] = manufacturer
            emit_state()
            self.update_progress.emit(f"Updated: {ip} - {name}")
        except Exception:
            pass

        self.resource_executor.submit(self._scan_resources, ip)
    
    def _scan_resources(self, ip):
        """Scan for printers and shared files on a device"""
        try:
            # Find printers
            printer = self.resource_scanner.find_printers(ip)
            if printer:
                self.add_resource.emit(ip, "Printer", printer)
            
            # Find file shares
            shares = self.resource_scanner.find_shares(ip)
            for share in shares:
                self.add_resource.emit(ip, "Share", share)
        except Exception:
            pass
    
    def _get_hostname(self, ip, progress_callback=None):
        """Get hostname from IP using multiple methods"""
        with self.hostname_cache_lock:
            cached_name = self.hostname_cache.get(ip)
            if cached_name:
                return cached_name

        def report_progress(method_number):
            if progress_callback:
                progress_callback(method_number, self.HOSTNAME_METHOD_COUNT)

        # Method 1: Reverse DNS lookup
        report_progress(1)
        try:
            hostname = socket.gethostbyaddr(ip)[0].split('.')[0]
            hostname = self._clean_hostname(hostname)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 2: Ping name resolution often exposes the Windows host name.
        report_progress(2)
        try:
            output = subprocess.check_output(
                ['ping', '-a', '-n', '1', '-w', str(self.ping_timeout_ms), ip],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=self.process_timeout_sec
            )
            match = re.search(r'Pinging\s+(.+?)\s+\[' + re.escape(ip) + r'\]', output, re.IGNORECASE)
            if match:
                hostname = self._clean_hostname(match.group(1))
                if hostname:
                    return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 3: NetBIOS via nbtstat is often the best source for Windows PC names.
        report_progress(3)
        try:
            output = subprocess.check_output(
                ['nbtstat', '-A', ip],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.2
            )
            hostname = self._extract_hostname_from_nbtstat(output)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 4: mDNS reverse lookup helps with Macs, Linux boxes, and IoT devices.
        report_progress(4)
        try:
            hostname = self._query_mdns_ptr(ip)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 5: DNS-SD browsing often exposes service instance names for non-Windows devices.
        report_progress(5)
        try:
            hostname = self._lookup_mdns_service_name(ip)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 6: SSDP/UPnP often exposes a friendlyName for consumer devices.
        report_progress(6)
        try:
            hostname = self._lookup_ssdp_friendly_name(ip)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 7: WS-Discovery can expose a FriendlyName for printers and Windows devices.
        report_progress(7)
        try:
            hostname = self._lookup_wsd_friendly_name(ip)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 8: SNMP sysName helps for switches, APs, printers, and managed devices.
        report_progress(8)
        try:
            hostname = self._lookup_snmp_sysname(ip)
            if hostname:
                return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 9: Resolve-DnsName can return PTR results where socket/nslookup fail.
        report_progress(9)
        try:
            output = subprocess.check_output(
                [
                    'powershell',
                    '-NoProfile',
                    '-Command',
                    (
                        f"$result = Resolve-DnsName -Name {ip} -Type PTR -ErrorAction SilentlyContinue; "
                        "if ($result) { $result.NameHost }"
                    )
                ],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.5
            )
            for line in output.split('\n'):
                hostname = self._clean_hostname(line)
                if hostname:
                    return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 10: nslookup can succeed where reverse DNS via socket fails.
        report_progress(10)
        try:
            output = subprocess.check_output(
                ['nslookup', ip],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.2
            )
            for line in output.split('\n'):
                line = line.strip()
                if line.lower().startswith('name:'):
                    hostname = self._clean_hostname(line.split(':', 1)[1].strip())
                    if hostname:
                        return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 11: Ask WMI for the computer system name.
        report_progress(11)
        try:
            output = subprocess.check_output(
                ['wmic', '/node:' + ip, 'computersystem', 'get', 'name'],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.5
            )
            for line in output.split('\n'):
                hostname = self._clean_hostname(line)
                if hostname:
                    return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 12: Ask WMI for DNS host names from NIC configuration.
        report_progress(12)
        try:
            output = subprocess.check_output(
                ['wmic', '/node:' + ip, 'nicconfig', 'get', 'dnshostname'],
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.5
            )
            for line in output.split('\n'):
                hostname = self._clean_hostname(line)
                if hostname:
                    return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        # Method 13: net view sometimes includes a server name banner.
        report_progress(13)
        try:
            output = subprocess.check_output(
                f'net view \\\\{ip}',
                stderr=subprocess.DEVNULL,
                text=True,
                timeout=1.2
            )
            first_line = output.split('\n', 1)[0].strip()
            match = re.search(r'\\\\([^\\\s]+)', first_line)
            if match:
                hostname = self._clean_hostname(match.group(1))
                if hostname:
                    return self._cache_hostname(ip, hostname)
        except Exception:
            pass

        return "Unknown"

    def _cache_hostname(self, ip, hostname):
        """Cache a discovered hostname for the current scan."""
        with self.hostname_cache_lock:
            self.hostname_cache[ip] = hostname
        return hostname

    def _lookup_ssdp_friendly_name(self, ip):
        """Resolve a host name from SSDP/UPnP metadata."""
        with self.ssdp_cache_lock:
            if self.ssdp_cache_populated:
                return self.ssdp_name_cache.get(ip)

        self._discover_ssdp_names_cached()
        with self.ssdp_cache_lock:
            return self.ssdp_name_cache.get(ip)

    def _discover_ssdp_names_cached(self):
        """Populate the SSDP cache once per scan."""
        with self.ssdp_cache_lock:
            if self.ssdp_cache_populated:
                return self.ssdp_name_cache

        discovered_names = self._discover_ssdp_names()

        with self.ssdp_cache_lock:
            if not self.ssdp_cache_populated:
                self.ssdp_name_cache = discovered_names
                self.ssdp_cache_populated = True
            return self.ssdp_name_cache

    def _discover_ssdp_names(self):
        """Discover friendly names via SSDP and UPnP device descriptions."""
        request = "\r\n".join([
            'M-SEARCH * HTTP/1.1',
            'HOST: 239.255.255.250:1900',
            'MAN: "ssdp:discover"',
            'MX: 1',
            'ST: ssdp:all',
            '',
            ''
        ]).encode('utf-8')

        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        discovered_names = {}
        location_cache = {}

        try:
            sock.settimeout(0.25)
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 2)
            sock.sendto(request, ('239.255.255.250', 1900))

            for _ in range(10):
                try:
                    data, addr = sock.recvfrom(8192)
                except socket.timeout:
                    break

                ip = addr[0]
                headers = self._parse_ssdp_headers(data)
                location = headers.get('location', '')
                if not location:
                    continue

                if location not in location_cache:
                    location_cache[location] = self._fetch_upnp_friendly_name(location)

                hostname = location_cache[location]
                if hostname and ip not in discovered_names:
                    discovered_names[ip] = hostname
        finally:
            sock.close()

        return discovered_names

    def _parse_ssdp_headers(self, data):
        """Parse an SSDP response into lowercase headers."""
        try:
            text = data.decode('utf-8', errors='ignore')
        except Exception:
            return {}

        headers = {}
        for line in text.split('\r\n'):
            if ':' not in line:
                continue
            key, value = line.split(':', 1)
            headers[key.strip().lower()] = value.strip()
        return headers

    def _fetch_upnp_friendly_name(self, location):
        """Fetch a UPnP device description and extract a friendly name."""
        try:
            request = urllib.request.Request(
                location,
                headers={'User-Agent': 'AdvancedIPScanner/1.0'}
            )
            with urllib.request.urlopen(request, timeout=1.2) as response:
                xml_text = response.read().decode('utf-8', errors='ignore')
        except Exception:
            return None

        return self._extract_friendly_name_from_xml(xml_text)

    def _lookup_wsd_friendly_name(self, ip):
        """Resolve a host name from WS-Discovery metadata."""
        with self.wsd_cache_lock:
            if self.wsd_cache_populated:
                return self.wsd_name_cache.get(ip)

        self._discover_wsd_names_cached()
        with self.wsd_cache_lock:
            return self.wsd_name_cache.get(ip)

    def _discover_wsd_names_cached(self):
        """Populate the WSD cache once per scan."""
        with self.wsd_cache_lock:
            if self.wsd_cache_populated:
                return self.wsd_name_cache

        discovered_names = self._discover_wsd_names()

        with self.wsd_cache_lock:
            if not self.wsd_cache_populated:
                self.wsd_name_cache = discovered_names
                self.wsd_cache_populated = True
            return self.wsd_name_cache

    def _discover_wsd_names(self):
        """Discover names through WS-Discovery metadata endpoints."""
        message_id = f'urn:uuid:{uuid.uuid4()}'
        probe = f"""<?xml version="1.0" encoding="UTF-8"?>
<e:Envelope xmlns:e="http://www.w3.org/2003/05/soap-envelope"
    xmlns:w="http://schemas.xmlsoap.org/ws/2004/08/addressing"
    xmlns:d="http://schemas.xmlsoap.org/ws/2005/04/discovery"
    xmlns:wsdp="http://schemas.xmlsoap.org/ws/2006/02/devprof">
  <e:Header>
    <w:MessageID>{message_id}</w:MessageID>
    <w:To>urn:schemas-xmlsoap-org:ws:2005:04:discovery</w:To>
    <w:Action>http://schemas.xmlsoap.org/ws/2005/04/discovery/Probe</w:Action>
  </e:Header>
  <e:Body>
    <d:Probe>
      <d:Types>wsdp:Device</d:Types>
    </d:Probe>
  </e:Body>
</e:Envelope>""".encode('utf-8')

        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        discovered_names = {}

        try:
            sock.settimeout(0.25)
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 2)
            sock.sendto(probe, ('239.255.255.250', 3702))

            xaddr_cache = {}
            for _ in range(10):
                try:
                    data, addr = sock.recvfrom(16384)
                except socket.timeout:
                    break

                ip = addr[0]
                xaddrs = self._extract_wsd_xaddrs(data)
                if not xaddrs:
                    continue

                hostname = None
                for xaddr in xaddrs:
                    if xaddr not in xaddr_cache:
                        xaddr_cache[xaddr] = self._fetch_wsd_friendly_name(xaddr)
                    hostname = xaddr_cache[xaddr]
                    if hostname:
                        break

                if hostname and ip not in discovered_names:
                    discovered_names[ip] = hostname
        finally:
            sock.close()

        return discovered_names

    def _extract_wsd_xaddrs(self, data):
        """Parse XAddrs from a WS-Discovery ProbeMatch response."""
        try:
            root = ET.fromstring(data.decode('utf-8', errors='ignore'))
        except ET.ParseError:
            return []

        xaddrs = []
        for element in root.iter():
            if element.tag.endswith('XAddrs') and element.text:
                xaddrs.extend(part.strip() for part in element.text.split() if part.strip())
        return xaddrs

    def _fetch_wsd_friendly_name(self, xaddr):
        """Fetch a WSD metadata endpoint and extract a friendly name."""
        try:
            request = urllib.request.Request(
                xaddr,
                headers={'User-Agent': 'AdvancedIPScanner/1.0'}
            )
            with urllib.request.urlopen(request, timeout=1.2) as response:
                xml_text = response.read().decode('utf-8', errors='ignore')
        except Exception:
            return None

        return self._extract_friendly_name_from_xml(xml_text)

    def _extract_friendly_name_from_xml(self, xml_text):
        """Extract the best human-friendly device name from XML metadata."""
        try:
            root = ET.fromstring(xml_text)
        except ET.ParseError:
            return None

        preferred_tags = ('FriendlyName', 'friendlyName', 'ModelName', 'modelName', 'DeviceName')
        for preferred_tag in preferred_tags:
            for element in root.iter():
                if element.tag.endswith(preferred_tag) and element.text:
                    candidate = element.text.strip()
                    hostname = self._clean_hostname(candidate)
                    if hostname:
                        return hostname
                    if candidate:
                        return candidate
        return None

    def _lookup_snmp_sysname(self, ip):
        """Resolve a host name from SNMP sysName using the public community."""
        with self.snmp_cache_lock:
            if ip in self.snmp_name_cache:
                return self.snmp_name_cache[ip]

        hostname = self._query_snmp_sysname(ip)

        with self.snmp_cache_lock:
            self.snmp_name_cache[ip] = hostname

        return hostname

    def _query_snmp_sysname(self, ip):
        """Query SNMP sysName.0 from a device."""
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.settimeout(0.35)
            request_id = (uuid.uuid4().int >> 96) & 0x7FFFFFFF
            packet = self._build_snmp_get_request(request_id, '1.3.6.1.2.1.1.5.0')
            sock.sendto(packet, (ip, 161))
            data, _ = sock.recvfrom(4096)
        except Exception:
            return None
        finally:
            sock.close()

        response = self._parse_snmp_response(data)
        if not response:
            return None

        hostname = self._clean_hostname(response)
        return hostname or response.strip()

    def _build_snmp_get_request(self, request_id, oid):
        """Build a minimal SNMPv2c get request packet."""
        version = self._ber_integer(1)
        community = self._ber_octet_string('public')
        oid_value = self._ber_oid(oid)
        null_value = self._ber_null()
        varbind = self._ber_sequence(oid_value + null_value)
        varbind_list = self._ber_sequence(varbind)
        pdu_body = (
            self._ber_integer(request_id) +
            self._ber_integer(0) +
            self._ber_integer(0) +
            varbind_list
        )
        pdu = self._ber_tlv(0xA0, pdu_body)
        return self._ber_sequence(version + community + pdu)

    def _parse_snmp_response(self, data):
        """Parse the first octet string value from an SNMP get response."""
        try:
            _, payload, _ = self._ber_read_tlv(data, 0)
            _, _, offset = self._ber_read_tlv(payload, 0)  # version
            _, _, offset = self._ber_read_tlv(payload, offset)  # community
            pdu_tag, pdu_payload, _ = self._ber_read_tlv(payload, offset)
            if pdu_tag != 0xA2:
                return None

            _, _, pdu_offset = self._ber_read_tlv(pdu_payload, 0)  # request-id
            _, _, pdu_offset = self._ber_read_tlv(pdu_payload, pdu_offset)  # error-status
            _, _, pdu_offset = self._ber_read_tlv(pdu_payload, pdu_offset)  # error-index
            _, varbind_list_payload, _ = self._ber_read_tlv(pdu_payload, pdu_offset)
            _, varbind_payload, _ = self._ber_read_tlv(varbind_list_payload, 0)
            _, _, vb_offset = self._ber_read_tlv(varbind_payload, 0)  # oid
            value_tag, value_payload, _ = self._ber_read_tlv(varbind_payload, vb_offset)
            if value_tag in (0x04, 0x40):
                return value_payload.decode('utf-8', errors='ignore').strip()
        except Exception:
            return None

        return None

    def _ber_tlv(self, tag, payload):
        """Encode a BER TLV."""
        return bytes([tag]) + self._ber_length(len(payload)) + payload

    def _ber_length(self, length):
        """Encode a BER length."""
        if length < 0x80:
            return bytes([length])

        parts = []
        while length:
            parts.insert(0, length & 0xFF)
            length >>= 8
        return bytes([0x80 | len(parts), *parts])

    def _ber_integer(self, value):
        """Encode a BER integer."""
        if value == 0:
            payload = b'\x00'
        else:
            payload = b''
            temp = value
            while temp:
                payload = bytes([temp & 0xFF]) + payload
                temp >>= 8
            if payload[0] & 0x80:
                payload = b'\x00' + payload
        return self._ber_tlv(0x02, payload)

    def _ber_octet_string(self, value):
        """Encode a BER octet string."""
        payload = value.encode('utf-8') if isinstance(value, str) else value
        return self._ber_tlv(0x04, payload)

    def _ber_null(self):
        """Encode a BER null."""
        return self._ber_tlv(0x05, b'')

    def _ber_sequence(self, payload):
        """Encode a BER sequence."""
        return self._ber_tlv(0x30, payload)

    def _ber_oid(self, oid):
        """Encode a BER object identifier."""
        parts = [int(part) for part in oid.split('.')]
        payload = bytes([parts[0] * 40 + parts[1]])
        for value in parts[2:]:
            encoded = [value & 0x7F]
            value >>= 7
            while value:
                encoded.insert(0, 0x80 | (value & 0x7F))
                value >>= 7
            payload += bytes(encoded)
        return self._ber_tlv(0x06, payload)

    def _ber_read_tlv(self, data, offset):
        """Read a BER TLV and return tag, payload, next offset."""
        tag = data[offset]
        offset += 1
        length, offset = self._ber_read_length(data, offset)
        payload = data[offset:offset + length]
        return tag, payload, offset + length

    def _ber_read_length(self, data, offset):
        """Read a BER length."""
        first = data[offset]
        offset += 1
        if first < 0x80:
            return first, offset

        count = first & 0x7F
        length = 0
        for _ in range(count):
            length = (length << 8) | data[offset]
            offset += 1
        return length, offset

    def _lookup_mdns_service_name(self, ip):
        """Resolve a host name from advertised mDNS/DNS-SD services."""
        with self.mdns_cache_lock:
            if self.mdns_cache_populated:
                return self.mdns_service_cache.get(ip)

        discovered_names = self._discover_mdns_service_names_cached()

        with self.mdns_cache_lock:
            return self.mdns_service_cache.get(ip)

    def _discover_mdns_service_names_cached(self):
        """Populate the shared mDNS cache once per scan."""
        with self.mdns_cache_lock:
            if self.mdns_cache_populated:
                return self.mdns_service_cache

        discovered_names = self._discover_mdns_service_names()

        with self.mdns_cache_lock:
            if not self.mdns_cache_populated:
                self.mdns_service_cache = discovered_names
                self.mdns_cache_populated = True
            return self.mdns_service_cache

    def _discover_mdns_service_names(self):
        """Browse common mDNS service types and map them back to IP addresses."""
        service_types = [
            '_apple-mobdev2._tcp.local',
            '_companion-link._tcp.local',
            '_airplay._tcp.local',
            '_raop._tcp.local',
            '_mediaremotetv._tcp.local',
            '_googlecast._tcp.local',
            '_spotify-connect._tcp.local',
            '_adb-tls-connect._tcp.local',
            '_adb-tls-pairing._tcp.local',
            '_hap._tcp.local',
            '_hap._udp.local',
            '_device-info._tcp.local',
            '_home-sharing._tcp.local',
            '_touch-able._tcp.local',
            '_ipp._tcp.local',
            '_http._tcp.local',
            '_rfb._tcp.local',
            '_ssh._tcp.local',
            '_smb._tcp.local',
            '_workstation._tcp.local',
            '_sleep-proxy._udp.local',
        ]

        discovered_names = {}
        discovered_scores = {}
        for index, service_type in enumerate(service_types):
            score = len(service_types) - index
            for ip, hostname in self._query_mdns_service_type(service_type).items():
                if not hostname:
                    continue
                hostname_score = self._score_service_hostname(hostname, service_type, score)
                if hostname_score > discovered_scores.get(ip, -1):
                    discovered_names[ip] = hostname
                    discovered_scores[ip] = hostname_score

        return discovered_names

    def _query_mdns_service_type(self, service_type):
        """Query a single DNS-SD service type over mDNS."""
        query = self._build_dns_query(service_type, qtype=12, unicast_response=False)
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        service_names = {}

        try:
            sock.settimeout(0.2)
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 1)
            sock.sendto(query, ('224.0.0.251', 5353))

            responses = []
            for _ in range(6):
                try:
                    data, _ = sock.recvfrom(8192)
                    responses.append(data)
                except socket.timeout:
                    break

            records = []
            for data in responses:
                records.extend(self._parse_dns_records(data))

            instance_to_target = {}
            target_to_ips = {}

            for record in records:
                if record['type'] == 33:
                    instance_to_target[record['name']] = record['target']
                elif record['type'] == 1 and record.get('address'):
                    target_to_ips.setdefault(record['name'], set()).add(record['address'])
                elif record['type'] == 28 and record.get('address'):
                    target_to_ips.setdefault(record['name'], set()).add(record['address'])

            for record in records:
                if record['type'] != 12 or record['name'] != service_type:
                    continue

                instance_name = record.get('target', '')
                target_host = instance_to_target.get(instance_name, '')
                hostname = self._extract_service_instance_label(instance_name, service_type)
                if not hostname and target_host:
                    hostname = self._clean_hostname(target_host)
                if not hostname:
                    continue

                for address in target_to_ips.get(target_host, set()):
                    service_names[address] = hostname
        finally:
            sock.close()

        return service_names

    def _parse_dns_records(self, data):
        """Parse resource records from a DNS response packet."""
        if len(data) < 12:
            return []

        _, _, qdcount, ancount, nscount, arcount = struct.unpack('!HHHHHH', data[:12])
        offset = 12

        for _ in range(qdcount):
            _, offset = self._read_dns_name(data, offset)
            offset += 4

        total_records = ancount + nscount + arcount
        records = []
        for _ in range(total_records):
            name, offset = self._read_dns_name(data, offset)
            if offset + 10 > len(data):
                break

            record_type, record_class, ttl, rdlength = struct.unpack('!HHIH', data[offset:offset + 10])
            offset += 10
            rdata_offset = offset
            rdata_end = offset + rdlength
            if rdata_end > len(data):
                break

            record = {
                'name': name,
                'type': record_type,
                'class': record_class,
                'ttl': ttl,
            }

            if record_type == 12:
                target, _ = self._read_dns_name(data, rdata_offset)
                record['target'] = target
            elif record_type == 33 and rdlength >= 6:
                _, _, port = struct.unpack('!HHH', data[rdata_offset:rdata_offset + 6])
                target, _ = self._read_dns_name(data, rdata_offset + 6)
                record['port'] = port
                record['target'] = target
            elif record_type == 1 and rdlength == 4:
                record['address'] = socket.inet_ntoa(data[rdata_offset:rdata_end])
            elif record_type == 28 and rdlength == 16:
                record['address'] = socket.inet_ntop(socket.AF_INET6, data[rdata_offset:rdata_end])

            records.append(record)
            offset = rdata_end

        return records

    def _extract_service_instance_label(self, instance_name, service_type):
        """Turn a DNS-SD instance name into a user-facing host label."""
        if not instance_name:
            return None

        suffix = f'.{service_type}'
        raw_label = instance_name
        if instance_name.endswith(suffix):
            raw_label = instance_name[:-len(suffix)]

        raw_label = raw_label.replace('\\032', ' ').replace('\\.', '.').strip()
        hostname = self._clean_hostname(raw_label)
        if hostname:
            return hostname

        if raw_label:
            return raw_label

        return None

    def _score_service_hostname(self, hostname, service_type, base_score):
        """Score how useful a discovered service label is as a device name."""
        score = base_score
        clean_name = (hostname or '').strip()
        lower_name = clean_name.lower()

        if not clean_name:
            return -1
        if re.fullmatch(r'[0-9a-f]{12,}', lower_name):
            score -= 40
        if re.fullmatch(r'[0-9a-f:-]{12,}', lower_name):
            score -= 25
        if any(token in lower_name for token in ('iphone', 'ipad', 'homepod', 'speaker', 'pixel', 'android', 'galaxy')):
            score += 18
        if service_type in {
            '_apple-mobdev2._tcp.local',
            '_airplay._tcp.local',
            '_raop._tcp.local',
            '_googlecast._tcp.local',
            '_spotify-connect._tcp.local',
            '_companion-link._tcp.local',
        }:
            score += 12

        return score

    def _query_mdns_ptr(self, ip):
        """Query mDNS for a reverse PTR record for non-Windows devices."""
        reverse_name = '.'.join(reversed(ip.split('.'))) + '.in-addr.arpa.local'
        query = self._build_dns_query(reverse_name, qtype=12, unicast_response=True)

        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
        try:
            sock.settimeout(0.45)
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 1)
            sock.sendto(query, ('224.0.0.251', 5353))

            for _ in range(2):
                try:
                    data, _ = sock.recvfrom(4096)
                except socket.timeout:
                    break

                hostname = self._extract_ptr_hostname_from_dns_response(data)
                hostname = self._clean_hostname(hostname)
                if hostname:
                    return hostname
        finally:
            sock.close()

        return None

    def _build_dns_query(self, name, qtype=12, unicast_response=False):
        """Build a minimal DNS query packet."""
        labels = []
        for part in name.split('.'):
            encoded = part.encode('utf-8', errors='ignore')
            labels.append(bytes([len(encoded)]) + encoded)

        qname = b''.join(labels) + b'\x00'
        qclass = 0x8001 if unicast_response else 0x0001
        header = struct.pack('!HHHHHH', 0, 0, 1, 0, 0, 0)
        question = qname + struct.pack('!HH', qtype, qclass)
        return header + question

    def _extract_ptr_hostname_from_dns_response(self, data):
        """Parse a PTR hostname from a DNS response packet."""
        if len(data) < 12:
            return None

        _, _, qdcount, ancount, nscount, arcount = struct.unpack('!HHHHHH', data[:12])
        offset = 12

        for _ in range(qdcount):
            _, offset = self._read_dns_name(data, offset)
            offset += 4

        total_records = ancount + nscount + arcount
        for _ in range(total_records):
            _, offset = self._read_dns_name(data, offset)
            if offset + 10 > len(data):
                return None

            record_type, _, _, rdlength = struct.unpack('!HHIH', data[offset:offset + 10])
            offset += 10
            if offset + rdlength > len(data):
                return None

            if record_type == 12:
                hostname, _ = self._read_dns_name(data, offset)
                return hostname

            offset += rdlength

        return None

    def _read_dns_name(self, data, offset):
        """Read a possibly compressed DNS name."""
        labels = []
        jumped = False
        next_offset = offset
        seen_offsets = set()

        while offset < len(data):
            if offset in seen_offsets:
                break
            seen_offsets.add(offset)

            length = data[offset]
            if length == 0:
                offset += 1
                if not jumped:
                    next_offset = offset
                break

            if length & 0xC0 == 0xC0:
                if offset + 1 >= len(data):
                    break
                pointer = ((length & 0x3F) << 8) | data[offset + 1]
                if not jumped:
                    next_offset = offset + 2
                offset = pointer
                jumped = True
                continue

            offset += 1
            label_bytes = data[offset:offset + length]
            labels.append(label_bytes.decode('utf-8', errors='ignore'))
            offset += length
            if not jumped:
                next_offset = offset

        return '.'.join(labels), next_offset

    def _extract_hostname_from_nbtstat(self, output):
        """Extract the most likely host name from nbtstat output."""
        preferred_suffixes = ('20', '03', '00')
        candidates = {suffix: [] for suffix in preferred_suffixes}

        for raw_line in output.split('\n'):
            line = raw_line.strip()
            match = re.match(r'^([^\s<]+)\s+<([0-9A-Fa-f]{2})>\s+(\w+)', line)
            if not match:
                continue

            raw_name, suffix, record_type = match.groups()
            if record_type.upper() == 'GROUP':
                continue

            hostname = self._clean_hostname(raw_name)
            if hostname and suffix in candidates:
                candidates[suffix].append(hostname)

        for suffix in preferred_suffixes:
            if candidates[suffix]:
                return candidates[suffix][0]

        return None

    def _clean_hostname(self, hostname):
        """Normalize hostnames and filter placeholders."""
        if not hostname:
            return None

        hostname = hostname.strip().strip('.').strip('[]')
        if '@' in hostname:
            hostname = hostname.rsplit('@', 1)[-1].strip()
        hostname = hostname.split('.')[0].strip()
        invalid_names = {
            'unknown', 'name', 'computername', 'localhost',
            'workgroup', 'dnshostname', 'msbrowse', '__msbrowse__'
        }

        if not hostname or hostname.lower() in invalid_names:
            return None
        if re.fullmatch(r'\d{1,3}(?:\.\d{1,3}){3}', hostname):
            return None
        if hostname.endswith(':'):
            return None

        return hostname

    def _normalize_mac_address(self, mac):
        """Normalize MAC addresses to uppercase colon notation."""
        clean_mac = re.sub(r'[^0-9A-Fa-f]', '', mac or '')
        if len(clean_mac) != 12:
            return ""
        return ':'.join(clean_mac[i:i + 2] for i in range(0, 12, 2)).upper()

    def _load_local_interface_macs(self):
        """Read local IPv4-to-MAC mappings from Windows adapter details."""
        with self.local_interface_mac_lock:
            if self.local_interface_mac_cache is not None:
                return self.local_interface_mac_cache

            mappings = {}
            try:
                output = subprocess.check_output(
                    ['ipconfig', '/all'],
                    text=True,
                    encoding='utf-8',
                    errors='ignore',
                    timeout=2
                )
                current_mac = ""

                for raw_line in output.splitlines():
                    line = raw_line.strip()
                    if not line:
                        current_mac = ""
                        continue

                    if 'Physical Address' in line:
                        match = re.search(r'([0-9A-Fa-f]{2}(?:-[0-9A-Fa-f]{2}){5})', line)
                        if match:
                            current_mac = self._normalize_mac_address(match.group(1))
                        continue

                    if not current_mac:
                        continue

                    if 'IPv4 Address' in line or 'Autoconfiguration IPv4 Address' in line:
                        match = re.search(r'(\d{1,3}(?:\.\d{1,3}){3})', line)
                        if match:
                            mappings[match.group(1)] = current_mac
            except Exception:
                pass

            self.local_interface_mac_cache = mappings
            return self.local_interface_mac_cache

    def _get_local_interface_mac(self, ip):
        """Return the MAC for one of this machine's own IPv4 addresses."""
        return self._load_local_interface_macs().get((ip or '').strip(), "")

    def _get_mac_from_arp(self, ip):
        """Get MAC address from ARP table"""
        local_mac = self._get_local_interface_mac(ip)
        if local_mac:
            return local_mac

        try:
            output = subprocess.check_output(['arp', '-a', ip], text=True)
            match = re.search(
                rf'{re.escape(ip)}\s+(([0-9a-fA-F]{{2}}[-:]){{5}}[0-9a-fA-F]{{2}})',
                output
            )
            if match:
                return self._normalize_mac_address(match.group(1))
        except Exception:
            pass

        try:
            output = subprocess.check_output(['arp', '-a'], text=True)
            match = re.search(
                rf'{re.escape(ip)}\s+(([0-9a-fA-F]{{2}}[-:]){{5}}[0-9a-fA-F]{{2}})',
                output
            )
            if match:
                return self._normalize_mac_address(match.group(1))
        except Exception:
            pass
        return "Unknown"

    def _get_manufacturer_from_mac(self, mac, progress_callback=None):
        """Get manufacturer from MAC address (first 3 octets)"""
        if mac == "Unknown":
            return ""

        def report_progress(method_number):
            if progress_callback:
                progress_callback(method_number, self.MANUFACTURER_METHOD_COUNT)

        normalized_mac = mac.replace('-', ':').upper()
        prefix = ':'.join(normalized_mac.split(':')[:3])

        with self.vendor_cache_lock:
            if prefix in self.vendor_cache:
                return self.vendor_cache[prefix]

        report_progress(1)
        manufacturer = self._lookup_vendor_from_registry(normalized_mac)
        if manufacturer:
            with self.vendor_cache_lock:
                self.vendor_cache[prefix] = manufacturer
            return manufacturer

        # Fast built-in hints for common cases before the online fallback.
        mac_prefixes = {
            "00:1A:A0": "Dell",
            "00:14:22": "Dell",
            "18:03:73": "Dell",
            "28:6B:35": "Dell",
            "00:0C:29": "VMware",
            "00:05:69": "VMware",
            "00:1C:14": "VMware",
            "08:00:27": "PCS Systemtechnik",
            "52:54:00": "QEMU",
            "00:15:5D": "Microsoft Hyper-V",
            "3C:52:82": "Hewlett Packard Enterprise",
            "48:0F:CF": "Hewlett Packard",
            "CC:3E:5F": "Hewlett Packard",
            "00:50:FC": "Edimax",
            "6C:F0:49": "GIGA-BYTE",
            "00:1B:78": "Hewlett Packard",
            "B8:27:EB": "Raspberry Pi",
            "DC:A6:32": "Raspberry Pi",
            "E4:5F:01": "Raspberry Pi",
            "F4:F5:D8": "Google",
            "3C:5A:B4": "Google Nest",
            "44:65:0D": "Amazon Technologies",
            "F0:D2:F1": "Amazon Technologies",
            "28:F0:76": "Apple",
            "3C:07:54": "Apple",
            "40:A6:D9": "Apple",
            "A4:B1:C1": "Apple",
            "D8:96:95": "Apple",
            "00:1F:3B": "Cisco",
            "00:25:9C": "Cisco",
            "2C:54:2D": "Cisco Meraki",
            "00:11:32": "Synology",
            "90:09:D0": "Synology",
            "00:17:88": "Philips",
            "EC:FA:BC": "Huawei",
            "F4:EC:38": "TP-Link",
            "50:C7:BF": "TP-Link",
            "C0:56:27": "Tenda",
            "9C:9D:7E": "Ubiquiti",
            "24:5A:4C": "Ubiquiti",
            "00:17:31": "ASUSTek",
            "2C:56:DC": "ASUSTek",
            "00:1E:8C": "Netgear",
            "20:0C:C8": "Netgear",
            "00:26:18": "Buffalo",
            "00:04:20": "Samsung",
            "FC:C2:DE": "Samsung",
            "00:23:69": "Hon Hai / Foxconn",
            "E0:CB:4E": "Intel",
            "F8:59:71": "Intel",
        }

        report_progress(2)
        if prefix in mac_prefixes:
            manufacturer = mac_prefixes[prefix]
            with self.vendor_cache_lock:
                self.vendor_cache[prefix] = manufacturer
            return manufacturer

        report_progress(3)
        manufacturer = self._lookup_vendor_online(normalized_mac)
        with self.vendor_cache_lock:
            self.vendor_cache[prefix] = manufacturer
        return manufacturer

    def _lookup_vendor_from_registry(self, mac):
        """Lookup vendor using locally cached IEEE and Wireshark data."""
        registry = self._ensure_vendor_registry_loaded()
        hex_mac = re.sub(r'[^0-9A-F]', '', mac.upper())
        if len(hex_mac) < 12:
            return ""

        mac_value = int(hex_mac[:12], 16)
        mask_map = registry.get('mask_map', {})

        for mask_bits in registry.get('mask_order', []):
            mask_entries = mask_map.get(str(mask_bits), {})
            mask = ((1 << mask_bits) - 1) << (48 - mask_bits)
            masked_value = mac_value & mask
            manufacturer = mask_entries.get(str(masked_value))
            if manufacturer and manufacturer.lower() != 'private':
                return manufacturer

        return ""

    def _ensure_vendor_registry_loaded(self):
        """Load the local vendor registry, refreshing from the network when needed."""
        with self.vendor_registry_lock:
            if self.vendor_registry_loaded:
                return self.vendor_registry

            registry = self._load_vendor_registry_from_disk()
            if registry is None:
                registry = self._refresh_vendor_registry()

            if registry is None:
                registry = {'mask_map': {}, 'mask_order': []}

            self.vendor_registry = registry
            self.vendor_registry_loaded = True
            return self.vendor_registry

    def _load_vendor_registry_from_disk(self):
        """Load the cached vendor registry from local SQLite storage."""
        try:
            with self._db_connect() as conn:
                row = conn.execute(
                    "SELECT payload, updated_at FROM app_cache WHERE cache_key = ?",
                    ('vendor_registry',)
                ).fetchone()
            if not row:
                return None

            payload, updated_at = row
            if (time.time() - float(updated_at)) > self.vendor_registry_max_age_sec:
                return None

            data = json.loads(payload)
            if isinstance(data, dict) and 'mask_map' in data and 'mask_order' in data:
                return data
        except Exception:
            return None

        return None

    def _refresh_vendor_registry(self):
        """Refresh the local vendor registry from broad public data sources."""
        registry = {'mask_map': {}, 'mask_order': []}

        self._merge_ieee_oui_text(registry)
        self._merge_wireshark_manuf(registry)
        self._finalize_vendor_registry(registry)

        try:
            with self._db_connect() as conn:
                conn.execute(
                    """
                    INSERT INTO app_cache (cache_key, payload, updated_at)
                    VALUES (?, ?, ?)
                    ON CONFLICT(cache_key) DO UPDATE SET
                        payload = excluded.payload,
                        updated_at = excluded.updated_at
                    """,
                    ('vendor_registry', json.dumps(registry), time.time())
                )
        except Exception:
            pass

        return registry

    def _merge_ieee_oui_text(self, registry):
        """Merge the official IEEE OUI public listing into the registry."""
        try:
            text = self._download_text('https://standards-oui.ieee.org/oui/oui.txt')
        except Exception:
            return

        current_prefix = None
        for raw_line in text.splitlines():
            line = raw_line.strip()
            match = re.match(r'^([0-9A-Fa-f]{2}(?:-[0-9A-Fa-f]{2}){2})\s+\(hex\)\s+(.+)$', line)
            if match:
                current_prefix = match.group(1).replace('-', '').upper()
                manufacturer = match.group(2).strip()
                self._register_vendor_entry(registry, current_prefix, 24, manufacturer, prefer_existing=False)
                continue

            if current_prefix is not None and '(base 16)' in line:
                parts = line.split('\t')
                if len(parts) >= 2:
                    manufacturer = parts[-1].strip()
                    if manufacturer:
                        self._register_vendor_entry(registry, current_prefix, 24, manufacturer, prefer_existing=False)
                current_prefix = None

    def _merge_wireshark_manuf(self, registry):
        """Merge Wireshark's manuf dataset for masked/range-based vendor entries."""
        manuf_text = None
        urls = [
            'https://www.wireshark.org/download/automated/data/manuf.gz',
            'https://www.wireshark.org/download/automated/data/manuf',
        ]

        for url in urls:
            try:
                if url.endswith('.gz'):
                    compressed = self._download_bytes(url)
                    manuf_text = gzip.decompress(compressed).decode('utf-8', errors='ignore')
                else:
                    manuf_text = self._download_text(url)
                if manuf_text:
                    break
            except Exception:
                continue

        if not manuf_text:
            return

        for raw_line in manuf_text.splitlines():
            line = raw_line.strip()
            if not line or line.startswith('#'):
                continue

            parts = line.split('\t')
            if len(parts) < 2:
                parts = re.split(r'\s{2,}', line, maxsplit=2)
            if len(parts) < 2:
                continue

            prefix_token = parts[0].strip()
            short_name = parts[1].strip()
            long_name = parts[2].strip() if len(parts) > 2 else ''
            manufacturer = long_name or short_name
            if not manufacturer:
                continue

            mask_bits = None
            if '/' in prefix_token:
                prefix_token, mask_text = prefix_token.split('/', 1)
                try:
                    mask_bits = int(mask_text)
                except ValueError:
                    continue

            hex_prefix = re.sub(r'[^0-9A-Fa-f]', '', prefix_token).upper()
            if not hex_prefix:
                continue

            if mask_bits is None:
                mask_bits = len(hex_prefix) * 4

            self._register_vendor_entry(registry, hex_prefix, mask_bits, manufacturer, prefer_existing=True)

    def _register_vendor_entry(self, registry, hex_prefix, mask_bits, manufacturer, prefer_existing):
        """Register one vendor entry in the mask map."""
        if not manufacturer:
            return

        cleaned_name = manufacturer.strip()
        if not cleaned_name:
            return

        prefix_value = int(hex_prefix, 16) << (48 - len(hex_prefix) * 4)
        mask = ((1 << mask_bits) - 1) << (48 - mask_bits)
        masked_value = prefix_value & mask

        mask_entries = registry['mask_map'].setdefault(str(mask_bits), {})
        existing = mask_entries.get(str(masked_value))
        if existing and prefer_existing:
            return

        mask_entries[str(masked_value)] = cleaned_name

    def _finalize_vendor_registry(self, registry):
        """Prepare lookup ordering for the vendor registry."""
        registry['mask_order'] = sorted(
            (int(mask_bits) for mask_bits in registry['mask_map'].keys()),
            reverse=True
        )

    def _download_text(self, url):
        """Download UTF-8 text with a browser-like user agent."""
        request = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(request, timeout=15) as response:
            return response.read().decode('utf-8', errors='ignore')

    def _download_bytes(self, url):
        """Download raw bytes with a browser-like user agent."""
        request = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(request, timeout=15) as response:
            return response.read()

    def _lookup_vendor_online(self, mac):
        """Lookup MAC vendor using an online API as a fallback."""
        try:
            request = urllib.request.Request(
                f'https://api.macvendors.com/{mac}',
                headers={'User-Agent': 'AdvancedIPScanner/1.0'}
            )
            with urllib.request.urlopen(request, timeout=1.5) as response:
                manufacturer = response.read().decode('utf-8', errors='ignore').strip()
                if manufacturer:
                    return manufacturer
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, ValueError):
            pass
        except Exception:
            pass

        return ""


class NetworkDiscoveryApp(QMainWindow):
    device_status_resolved = pyqtSignal(str, str, str)
    device_status_refresh_finished = pyqtSignal(int)

    def __init__(self):
        super().__init__()
        self.scanner = NetworkScanner()
        self.scanner.update_progress.connect(self.update_status)
        self.scanner.add_device.connect(self.add_device_to_tree)
        self.scanner.add_resource.connect(self.add_resource_to_tree)
        self.scanner.scan_complete.connect(self.scan_finished)
        self.scanner.status_update.connect(self.update_device_count)
        self.scanner.progress_update.connect(self.update_progress)
        self.device_status_resolved.connect(self._apply_resolved_device_status)
        self.device_status_refresh_finished.connect(self._finish_status_refresh)
        
        self.device_items = {}  # Track device tree items by IP
        self.is_scanning = False
        self.is_refreshing_status = False
        self.storage_db_path = self.scanner.storage_db_path
        self.favorites = {}  # Store favorites as {ip: device_info}
        self.nicknames = {}
        self.device_status_cache = {}
        self._ensure_storage_db()
        self.settings = self.default_settings()
        self.load_settings()
        self.load_nicknames()
        self.load_device_statuses()
        self.load_favorites()
        self.init_ui()
        self.populate_favorites_tab()

    def _db_connect(self):
        """Create a short-lived SQLite connection for local storage."""
        return sqlite3.connect(self.storage_db_path, timeout=5)

    def _ensure_storage_db(self):
        """Create local storage tables if needed."""
        try:
            with self._db_connect() as conn:
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS app_settings (
                        setting_key TEXT PRIMARY KEY,
                        setting_value TEXT NOT NULL
                    )
                """)
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS favorites (
                        favorite_key TEXT PRIMARY KEY,
                        ip TEXT NOT NULL,
                        name TEXT NOT NULL,
                        manufacturer TEXT NOT NULL,
                        mac TEXT NOT NULL
                    )
                """)
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS device_nicknames (
                        device_key TEXT PRIMARY KEY,
                        nickname TEXT NOT NULL
                    )
                """)
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS device_statuses (
                        device_key TEXT PRIMARY KEY,
                        status TEXT NOT NULL,
                        updated_at REAL NOT NULL
                    )
                """)
        except Exception:
            pass

    def default_settings(self):
        """Build the default persisted settings for the app."""
        return {
            'max_workers': self.scanner.max_workers,
            'detail_workers': self.scanner.detail_workers,
            'resource_workers': self.scanner.resource_workers,
            'ping_timeout_ms': self.scanner.ping_timeout_ms,
            'process_timeout_sec': self.scanner.process_timeout_sec,
            'named_only_default': False,
        }

    def load_settings(self):
        """Load saved settings from local SQLite storage."""
        try:
            with self._db_connect() as conn:
                rows = conn.execute(
                    "SELECT setting_key, setting_value FROM app_settings"
                ).fetchall()
            for setting_key, setting_value in rows:
                try:
                    self.settings[setting_key] = json.loads(setting_value)
                except Exception:
                    self.settings[setting_key] = setting_value
        except Exception:
            pass

        self.scanner.apply_runtime_settings(
            max_workers=self.settings.get('max_workers'),
            detail_workers=self.settings.get('detail_workers'),
            resource_workers=self.settings.get('resource_workers'),
            ping_timeout_ms=self.settings.get('ping_timeout_ms'),
            process_timeout_sec=self.settings.get('process_timeout_sec'),
        )

    def save_settings(self):
        """Persist settings to local SQLite storage."""
        try:
            with self._db_connect() as conn:
                for setting_key, setting_value in self.settings.items():
                    conn.execute(
                        """
                        INSERT INTO app_settings (setting_key, setting_value)
                        VALUES (?, ?)
                        ON CONFLICT(setting_key) DO UPDATE SET
                            setting_value = excluded.setting_value
                        """,
                        (setting_key, json.dumps(setting_value))
                    )
        except Exception:
            pass

    def load_nicknames(self):
        """Load custom device nicknames from local SQLite storage."""
        self.nicknames = {}
        try:
            with self._db_connect() as conn:
                rows = conn.execute(
                    "SELECT device_key, nickname FROM device_nicknames"
                ).fetchall()
            for device_key, nickname in rows:
                clean_nickname = (nickname or '').strip()
                if device_key and clean_nickname:
                    self.nicknames[device_key] = clean_nickname
        except Exception:
            self.nicknames = {}

    def save_nicknames(self):
        """Persist custom device nicknames to local SQLite storage."""
        try:
            with self._db_connect() as conn:
                conn.execute("DELETE FROM device_nicknames")
                for device_key, nickname in self.nicknames.items():
                    conn.execute(
                        """
                        INSERT INTO device_nicknames (device_key, nickname)
                        VALUES (?, ?)
                        """,
                        (device_key, nickname)
                    )
        except Exception:
            pass

    def load_device_statuses(self):
        """Load cached device statuses from local SQLite storage."""
        self.device_status_cache = {}
        try:
            with self._db_connect() as conn:
                rows = conn.execute(
                    "SELECT device_key, status FROM device_statuses"
                ).fetchall()
            for device_key, status in rows:
                if device_key and status:
                    self.device_status_cache[device_key] = status
        except Exception:
            self.device_status_cache = {}

    def save_device_status(self, ip, mac, status_text):
        """Persist one device status to local SQLite storage."""
        device_key = self.get_favorite_key(ip, mac)
        if not device_key or not status_text:
            return

        self.device_status_cache[device_key] = status_text
        try:
            with self._db_connect() as conn:
                conn.execute(
                    """
                    INSERT INTO device_statuses (device_key, status, updated_at)
                    VALUES (?, ?, ?)
                    ON CONFLICT(device_key) DO UPDATE SET
                        status = excluded.status,
                        updated_at = excluded.updated_at
                    """,
                    (device_key, status_text, time.time())
                )
        except Exception:
            pass

    def get_cached_device_status(self, ip, mac=''):
        """Return the last known status for a device without pinging it."""
        device_key = self.get_favorite_key(ip, mac)
        if device_key and device_key in self.device_status_cache:
            return self.device_status_cache[device_key]
        ip_key = self.get_favorite_key(ip, '')
        if ip_key and ip_key in self.device_status_cache:
            return self.device_status_cache[ip_key]
        return 'Unknown'

    def get_favorite_key(self, ip='', mac=''):
        """Build a stable favorite key, preferring MAC over IP."""
        mac = (mac or '').strip()
        ip = (ip or '').strip()

        if mac and mac.lower() != 'unknown':
            return f"mac:{mac.upper()}"
        if ip:
            return f"ip:{ip}"
        return ''

    def get_item_favorite_key(self, item):
        """Get favorite key for a tree item."""
        if item is None:
            return ''
        return self.get_favorite_key(item.text(2), item.text(4))

    def get_device_nickname(self, ip='', mac=''):
        """Return a saved nickname for a device when available."""
        device_key = self.get_favorite_key(ip, mac)
        if device_key and device_key in self.nicknames:
            return self.nicknames[device_key]

        if ip:
            for saved_key, nickname in self.nicknames.items():
                if saved_key == f'ip:{ip}':
                    return nickname
            favorite_key, _ = self.find_favorite_by_ip(ip)
            if favorite_key and favorite_key in self.nicknames:
                return self.nicknames[favorite_key]

        return ''

    def set_device_nickname(self, ip, mac, nickname):
        """Persist a nickname for a device."""
        device_key = self.get_favorite_key(ip, mac)
        if not device_key:
            return False

        clean_nickname = (nickname or '').strip()
        if not clean_nickname:
            return False

        self.nicknames[device_key] = clean_nickname
        self.save_nicknames()
        return True

    def clear_device_nickname(self, ip, mac):
        """Remove a persisted nickname for a device."""
        removed = False
        device_key = self.get_favorite_key(ip, mac)
        for key in {device_key, f'ip:{(ip or "").strip()}'}:
            if key and key in self.nicknames:
                del self.nicknames[key]
                removed = True
        if removed:
            self.save_nicknames()
        return removed

    def get_display_name(self, raw_name, ip='', mac=''):
        """Prefer a custom nickname over the discovered device name."""
        nickname = self.get_device_nickname(ip, mac)
        return nickname or raw_name

    def find_favorite_by_ip(self, ip):
        """Find a favorite entry by the saved IP value."""
        for favorite_key, device_info in self.favorites.items():
            if device_info.get('ip') == ip:
                return favorite_key, device_info
        return None, None

    def is_favorited_device(self, ip='', mac=''):
        """Check whether a device is favorited."""
        favorite_key = self.get_favorite_key(ip, mac)
        if favorite_key and favorite_key in self.favorites:
            return True

        _, device_info = self.find_favorite_by_ip(ip)
        return device_info is not None

    def format_device_label(self, name, ip):
        """Format the visible device label."""
        clean_name = (name or '').strip()
        clean_ip = (ip or '').strip()

        loading_match = re.match(r'^__NAME_LOADING__:(\d+):(\d+)$', clean_name)
        if clean_name == '__LOADING__':
            return f'(loading name 1/1) ({clean_ip})' if clean_ip else '(loading name 1/1)'
        if loading_match:
            current_method, total_methods = loading_match.groups()
            loading_text = f'(loading name {current_method}/{total_methods})'
            return f'{loading_text} ({clean_ip})' if clean_ip else loading_text
        if not clean_name or clean_name.lower() == 'unknown':
            return clean_ip or 'Unknown'
        if not clean_ip:
            return clean_name
        return f'{clean_name} ({clean_ip})'

    def item_has_display_name(self, item):
        """Return True if the item has either a nickname or a discovered name."""
        if item is None:
            return False
        nickname = (item.data(1, Qt.UserRole + 1) or '').strip()
        if nickname:
            return True
        return self.has_found_name(item.data(1, Qt.UserRole) or '')

    def has_found_name(self, name):
        """Return True when the scanner found a usable host name."""
        clean_name = (name or '').strip()
        return bool(
            clean_name
            and clean_name.lower() != 'unknown'
            and clean_name != '__LOADING__'
            and not clean_name.startswith('__NAME_LOADING__:')
        )

    def format_manufacturer_label(self, manufacturer):
        """Format the visible manufacturer label."""
        clean_manufacturer = (manufacturer or '').strip()
        loading_match = re.match(r'^__MANUFACTURER_LOADING__:(\d+):(\d+)$', clean_manufacturer)
        if loading_match:
            current_method, total_methods = loading_match.groups()
            return f'(loading manufacturer {current_method}/{total_methods})'
        return clean_manufacturer
    
    def init_ui(self):
        """Initialize the user interface"""
        self.setWindowTitle('Advanced IP Scanner')
        self.setGeometry(100, 100, 1000, 700)
        self.setStyleSheet("""
            QMainWindow { background-color: #f0f0f0; }
            QPushButton { 
                background-color: #4CAF50; 
                color: white; 
                padding: 5px; 
                border-radius: 3px;
                font-weight: bold;
            }
            QPushButton:hover { background-color: #45a049; }
        """)
        
        # Create menu bar
        menubar = self.menuBar()
        file_menu = menubar.addMenu('File')
        view_menu = menubar.addMenu('View')
        settings_menu = menubar.addMenu('Settings')
        help_menu = menubar.addMenu('Help')
        
        # Create central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(10, 10, 10, 10)
        
        # Create toolbar
        toolbar = QToolBar()
        toolbar.setMovable(False)
        self.addToolBar(toolbar)
        
        # Scan button
        self.scan_btn = QPushButton('Scan')
        self.scan_btn.setMaximumWidth(80)
        self.scan_btn.clicked.connect(self.start_scan)
        toolbar.addWidget(self.scan_btn)
        
        # Pause button
        pause_btn = QPushButton('Pause')
        pause_btn.setMaximumWidth(80)
        toolbar.addWidget(pause_btn)
        
        toolbar.addSeparator()
        
        # IP range input
        input_layout = QHBoxLayout()
        ip_label = QLabel('IP range:')
        self.ip_range_input = QLineEdit()
        self.ip_range_input.setText('192.168.0.1-254')
        self.ip_range_input.setPlaceholderText('Example: 192.168.0.1-100, 192.168.0.1/24')
        self.ip_range_input.setMaximumWidth(300)
        input_layout.addWidget(ip_label)
        input_layout.addWidget(self.ip_range_input)
        
        # Create a widget to hold the input layout
        input_widget = QWidget()
        input_widget.setLayout(input_layout)
        
        # Add to main layout
        main_layout.addWidget(input_widget)
        
        # Progress bar
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        self.progress_bar.setStyleSheet("""
            QProgressBar {
                border: 2px solid grey;
                border-radius: 5px;
                text-align: center;
            }
            QProgressBar::chunk {
                background-color: #4CAF50;
            }
        """)
        main_layout.addWidget(self.progress_bar)
        
        # Status and device count
        info_layout = QHBoxLayout()
        self.status_label = QLabel('Ready')
        self.count_label = QLabel('0 alive, 0 dead, 0 unknown')
        info_layout.addWidget(self.status_label)
        info_layout.addStretch()
        info_layout.addWidget(self.count_label)
        main_layout.addLayout(info_layout)
        
        # Results tabs
        tabs = QTabWidget()
        
        # Results tab
        results_tab = QWidget()
        results_layout = QVBoxLayout(results_tab)
        
        # Tree widget for hierarchical display
        self.tree = QTreeWidget()
        self.tree.setColumnCount(5)
        self.tree.setHeaderLabels(['Status', 'Name', 'IP', 'Manufacturer', 'MAC address'])
        self.tree.setColumnWidth(0, 60)
        self.tree.setColumnWidth(1, 200)
        self.tree.setColumnWidth(2, 150)
        self.tree.setColumnWidth(3, 200)
        self.tree.setColumnWidth(4, 150)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self.show_context_menu)
        results_layout.addWidget(self.tree)
        tabs.addTab(results_tab, 'Results')
        
        # Favorites tab
        favorites_tab = QWidget()
        favorites_layout = QVBoxLayout(favorites_tab)
        
        # Favorites tree widget
        self.favorites_tree = QTreeWidget()
        self.favorites_tree.setColumnCount(5)
        self.favorites_tree.setHeaderLabels(['Status', 'Name', 'IP', 'Manufacturer', 'MAC address'])
        self.favorites_tree.setColumnWidth(0, 60)
        self.favorites_tree.setColumnWidth(1, 200)
        self.favorites_tree.setColumnWidth(2, 150)
        self.favorites_tree.setColumnWidth(3, 200)
        self.favorites_tree.setColumnWidth(4, 150)
        self.favorites_tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.favorites_tree.customContextMenuRequested.connect(self.show_favorites_context_menu)
        favorites_layout.addWidget(self.favorites_tree)
        tabs.addTab(favorites_tab, 'Favorites')
        
        main_layout.addWidget(tabs)
        
        # Status bar
        self.statusBar().showMessage('Ready to scan')
    
    def start_scan(self):
        """Start network scan"""
        ip_range = self.ip_range_input.text().strip()
        if not ip_range:
            self.update_status("Please enter an IP range")
            return
        
        # Reset UI
        self.tree.clear()
        self.device_items = {}
        self.scanner.alive_count = 0
        self.scanner.dead_count = 0
        self.scanner.scanned_count = 0
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)
        self.progress_bar.setFormat("Starting scan...")
        self.scan_btn.setEnabled(False)
        self.scan_btn.setText("Scanning...")
        self.is_scanning = True
        
        self.update_status(f"Scanning {ip_range}...")
        self.count_label.setText("0 alive, 0 dead, 0 unknown")
        
        # Parse IP range and start scan in background thread
        ips = self.scanner.parse_ip_range(ip_range)
        scan_thread = threading.Thread(target=self._run_scan, args=(ips,))
        scan_thread.daemon = True
        scan_thread.start()
    
    def _run_scan(self, ips):
        """Run scan in background"""
        try:
            self.scanner.scan_ips(ips)
            self.scanner.scan_complete.emit()
        except Exception as e:
            self.update_status(f"Scan error: {str(e)}")
            self.scanner.scan_complete.emit()
    
    def add_device_to_tree(self, device):
        """Add device to tree widget"""
        item = QTreeWidgetItem()
        item.setText(0, "●")  # Status indicator
        item.setText(1, device['name'])
        item.setText(2, device['ip'])
        item.setText(3, self.format_manufacturer_label(device['manufacturer']))
        item.setText(4, device['mac'])
        
        # Set color
        for i in range(5):
            item.setForeground(i, QColor(0, 100, 200))
        
        self.tree.addTopLevelItem(item)
        self.device_items[device['ip']] = item
    
    def add_resource_to_tree(self, ip, resource_type, resource_name):
        """Add resource (printer/share) to tree under device"""
        if ip in self.device_items:
            device_item = self.device_items[ip]
            
            # Check if resource type item exists
            resource_item = None
            for i in range(device_item.childCount()):
                child = device_item.child(i)
                if child.text(1) == resource_type:
                    resource_item = child
                    break
            
            # Create resource type item if not exists
            if not resource_item:
                resource_item = QTreeWidgetItem(device_item)
                resource_item.setText(1, resource_type)
                for j in range(5):
                    resource_item.setForeground(j, QColor(150, 100, 0))
            
            # Add actual resource
            res_detail = QTreeWidgetItem(resource_item)
            res_detail.setText(1, resource_name)
            for j in range(5):
                res_detail.setForeground(j, QColor(100, 100, 100))
    
    def update_status(self, message):
        """Update status message"""
        self.status_label.setText(message)
        self.statusBar().showMessage(message)
    
    def update_device_count(self, alive, dead, unknown):
        """Update device count display"""
        self.count_label.setText(f'{alive} alive, {dead} dead, {unknown} unknown')
    
    def update_progress(self, current, total):
        """Update progress bar"""
        if total > 0:
            percentage = int((current / total) * 100)
            self.progress_bar.setValue(percentage)
            self.progress_bar.setFormat(f"Scanning: {current}/{total} IPs ({percentage}%)")
            
            # Update counts in real-time
            if self.is_scanning:
                self.count_label.setText(
                    f'{self.scanner.alive_count} alive, '
                    f'{self.scanner.dead_count} dead, '
                    f'{total - current} remaining'
                )
    
    def scan_finished(self):
        """Called when scan is complete"""
        self.is_scanning = False
        self.progress_bar.setFormat(f"100% - Scan complete")
        self.progress_bar.setValue(100)
        self.scan_btn.setEnabled(True)
        self.scan_btn.setText("Scan")
        self.update_status(f'Scan complete - Found {self.scanner.alive_count} devices')
        self.update_device_count(self.scanner.alive_count, self.scanner.dead_count, 0)
    
    def show_context_menu(self, position):
        """Show right-click context menu for tree items"""
        item = self.tree.itemAt(position)
        if item is None or item.parent() is not None:
            return  # Only show menu for top-level devices
        
        ip = item.text(2)
        if not ip:
            return
        
        menu = QMenu()
        
        if ip in self.favorites:
            action = menu.addAction("Remove from Favorites ⭐")
            action.triggered.connect(lambda: self.toggle_favorite(ip, item))
        else:
            action = menu.addAction("Add to Favorites ☆")
            action.triggered.connect(lambda: self.toggle_favorite(ip, item))
        
        menu.exec_(self.tree.mapToGlobal(position))
    
    def show_favorites_context_menu(self, position):
        """Show right-click context menu for favorites tree items"""
        item = self.favorites_tree.itemAt(position)
        if item is None or item.parent() is not None:
            return  # Only show menu for top-level devices
        
        ip = item.text(2)
        if not ip:
            return
        
        menu = QMenu()
        action = menu.addAction("Remove from Favorites ⭐")
        action.triggered.connect(lambda: self.remove_favorite(ip))
        
        menu.exec_(self.favorites_tree.mapToGlobal(position))
    
    def toggle_favorite(self, ip, item):
        """Toggle favorite status for a device"""
        if ip in self.favorites:
            self.remove_favorite(ip)
        else:
            self.add_favorite(ip, item)
    
    def add_favorite(self, ip, item):
        """Add device to favorites"""
        device_info = {
            'ip': ip,
            'name': item.text(1),
            'manufacturer': item.text(3),
            'mac': item.text(4)
        }
        self.favorites[ip] = device_info
        self.save_favorites()
        self.populate_favorites_tab()
        self.update_status(f"Added {device_info['name']} to favorites")
    
    def remove_favorite(self, ip):
        """Remove device from favorites"""
        if ip in self.favorites:
            name = self.favorites[ip]['name']
            del self.favorites[ip]
            self.save_favorites()
            self.populate_favorites_tab()
            self.update_status(f"Removed {name} from favorites")
    
    def save_favorites(self):
        """Persist favorites to local SQLite storage."""
        try:
            with self._db_connect() as conn:
                conn.execute("DELETE FROM favorites")
                for favorite_key, device_info in self.favorites.items():
                    conn.execute(
                        """
                        INSERT INTO favorites (favorite_key, ip, name, manufacturer, mac)
                        VALUES (?, ?, ?, ?, ?)
                        """,
                        (
                            favorite_key,
                            device_info.get('ip', ''),
                            device_info.get('name', ''),
                            device_info.get('manufacturer', ''),
                            device_info.get('mac', ''),
                        )
                    )
        except Exception:
            pass

    def load_favorites(self):
        """Load favorites from local SQLite storage."""
        self.favorites = {}
        try:
            with self._db_connect() as conn:
                rows = conn.execute(
                    "SELECT favorite_key, ip, name, manufacturer, mac FROM favorites"
                ).fetchall()
            for favorite_key, ip, name, manufacturer, mac in rows:
                resolved_key = self.get_favorite_key(ip, mac) or favorite_key
                self.favorites[resolved_key] = {
                    'favorite_key': resolved_key,
                    'ip': ip,
                    'name': name,
                    'manufacturer': manufacturer,
                    'mac': mac,
                }
        except Exception:
            self.favorites = {}
    
    def populate_favorites_tab(self):
        """Populate the favorites tab with saved favorites"""
        self.favorites_tree.clear()
        
        for ip, device_info in self.favorites.items():
            item = QTreeWidgetItem()
            item.setText(0, "⭐")  # Favorite indicator
            item.setText(1, device_info['name'])
            item.setText(2, device_info['ip'])
            item.setText(3, self.format_manufacturer_label(device_info['manufacturer']))
            item.setText(4, device_info['mac'])
            
            # Set color
            for i in range(5):
                item.setForeground(i, QColor(200, 130, 0))  # Gold/orange color for favorites
            
            self.favorites_tree.addTopLevelItem(item)

    def add_device_to_tree(self, device):
        """Add device to tree widget."""
        item = QTreeWidgetItem()
        is_favorite = self.is_favorited_device(device['ip'], device['mac'])

        item.setText(0, "★" if is_favorite else "●")
        item.setText(1, device['name'])
        item.setText(2, device['ip'])
        item.setText(3, self.format_manufacturer_label(device['manufacturer']))
        item.setText(4, device['mac'])

        for i in range(5):
            item.setForeground(i, QColor(200, 130, 0) if is_favorite else QColor(0, 100, 200))

        if is_favorite:
            self.refresh_favorite_from_device(device)

        self.tree.addTopLevelItem(item)
        self.device_items[device['ip']] = item

    def show_context_menu(self, position):
        """Show right-click context menu for tree items."""
        item = self.tree.itemAt(position)
        if item is None or item.parent() is not None:
            return

        favorite_key = self.get_item_favorite_key(item)
        if not item.text(2) and not favorite_key:
            return

        menu = QMenu()
        action = menu.addAction(
            "Unfavorite" if self.is_favorited_device(item.text(2), item.text(4)) else "Favorite"
        )
        action.triggered.connect(lambda: self.toggle_favorite(item))
        nickname_action = menu.addAction("Set Nickname")
        nickname_action.triggered.connect(lambda: self.prompt_for_nickname(item))
        if self.get_device_nickname(item.text(2), item.text(4)):
            clear_nickname_action = menu.addAction("Clear Nickname")
            clear_nickname_action.triggered.connect(lambda: self.clear_nickname_for_item(item))
        menu.exec_(self.tree.mapToGlobal(position))

    def show_favorites_context_menu(self, position):
        """Show right-click context menu for favorites tree items."""
        item = self.favorites_tree.itemAt(position)
        if item is None or item.parent() is not None:
            return

        favorite_key = item.data(0, Qt.UserRole)
        if not favorite_key:
            return

        menu = QMenu()
        action = menu.addAction("Unfavorite")
        action.triggered.connect(lambda: self.remove_favorite(favorite_key))
        nickname_action = menu.addAction("Set Nickname")
        nickname_action.triggered.connect(lambda: self.prompt_for_nickname(item))
        if self.get_device_nickname(item.text(2), item.text(4)):
            clear_nickname_action = menu.addAction("Clear Nickname")
            clear_nickname_action.triggered.connect(lambda: self.clear_nickname_for_item(item))
        menu.exec_(self.favorites_tree.mapToGlobal(position))

    def prompt_for_nickname(self, item):
        """Prompt the user to set a custom nickname for a device."""
        ip = item.text(2)
        mac = item.text(4)
        current_nickname = self.get_device_nickname(ip, mac)
        nickname, ok = QInputDialog.getText(
            self,
            'Set Nickname',
            f'Nickname for {ip}:',
            text=current_nickname
        )
        if not ok:
            return

        clean_nickname = (nickname or '').strip()
        if not clean_nickname:
            self.clear_nickname_for_item(item)
            return

        if self.set_device_nickname(ip, mac, clean_nickname):
            self.refresh_all_device_labels()
            self.update_status(f'Nickname saved for {ip}')

    def clear_nickname_for_item(self, item):
        """Clear a custom nickname for a device item."""
        ip = item.text(2)
        mac = item.text(4)
        if self.clear_device_nickname(ip, mac):
            self.refresh_all_device_labels()
            self.update_status(f'Nickname cleared for {ip}')

    def toggle_favorite(self, item):
        """Toggle favorite status for a device."""
        favorite_key = self.get_item_favorite_key(item)
        if favorite_key in self.favorites:
            self.remove_favorite(favorite_key)
            return

        existing_key, _ = self.find_favorite_by_ip(item.text(2))
        if existing_key:
            self.remove_favorite(existing_key)
            return

        self.add_favorite(item)

    def add_favorite(self, item):
        """Add device to favorites."""
        favorite_key = self.get_item_favorite_key(item)
        raw_name = item.data(1, Qt.UserRole) or item.text(1)
        device_info = {
            'favorite_key': favorite_key,
            'ip': item.text(2),
            'name': raw_name,
            'manufacturer': item.text(3),
            'mac': item.text(4)
        }
        self.favorites[favorite_key] = device_info
        self.save_favorites()
        self.populate_favorites_tab()
        self.refresh_results_tree_favorites()
        self.update_status(f"Added {device_info['name']} to favorites")

    def remove_favorite(self, favorite_key):
        """Remove device from favorites."""
        if favorite_key in self.favorites:
            name = self.favorites[favorite_key]['name']
            del self.favorites[favorite_key]
            self.save_favorites()
            self.populate_favorites_tab()
            self.refresh_results_tree_favorites()
            self.update_status(f"Removed {name} from favorites")

    def refresh_favorite_from_device(self, device):
        """Update a saved favorite with the latest scan details."""
        favorite_key = self.get_favorite_key(device['ip'], device['mac'])
        existing_key, _ = self.find_favorite_by_ip(device['ip'])

        if favorite_key in self.favorites:
            target_key = favorite_key
        elif existing_key:
            target_key = existing_key
        else:
            return

        updated_device_info = {
            'favorite_key': favorite_key,
            'ip': device['ip'],
            'name': device['name'],
            'manufacturer': device['manufacturer'],
            'mac': device['mac']
        }

        if target_key != favorite_key:
            del self.favorites[target_key]

        self.favorites[favorite_key] = updated_device_info
        self.save_favorites()
        self.populate_favorites_tab()

    def refresh_all_device_labels(self):
        """Re-render names in both trees after nickname changes."""
        for ip, item in self.device_items.items():
            raw_name = item.data(1, Qt.UserRole) or ''
            nickname = self.get_device_nickname(ip, item.text(4))
            item.setData(1, Qt.UserRole + 1, nickname)
            item.setText(1, self.format_device_label(self.get_display_name(raw_name, ip, item.text(4)), ip))

        self.sort_device_tree(self.tree)
        self.populate_favorites_tab()
        self.refresh_results_tree_favorites()
        self.apply_filter()

    def refresh_all_statuses(self):
        """Re-ping listed devices sequentially in the background."""
        if self.is_refreshing_status:
            return

        devices_to_refresh = []
        seen_ips = set()

        for ip, item in self.device_items.items():
            if not ip or ip in seen_ips:
                continue
            seen_ips.add(ip)
            devices_to_refresh.append((ip, item.text(4)))
            is_favorite = self.is_favorited_device(ip, item.text(4))
            item.setText(0, 'Loading')
            self._style_device_item(item, is_favorite, 'Loading')

        for index in range(self.favorites_tree.topLevelItemCount()):
            item = self.favorites_tree.topLevelItem(index)
            ip = item.text(2)
            if not ip:
                continue
            item.setText(0, 'Loading')
            self._style_device_item(item, True, 'Loading')

        if not devices_to_refresh:
            self.update_status('No devices to refresh')
            return

        self.is_refreshing_status = True
        self.refresh_status_btn.setEnabled(False)
        self.update_status(f'Refreshing status for {len(devices_to_refresh)} devices...')
        self.apply_filter()

        refresh_thread = threading.Thread(
            target=self._refresh_statuses_worker,
            args=(devices_to_refresh,),
            daemon=True
        )
        refresh_thread.start()

    def _refresh_statuses_worker(self, devices_to_refresh):
        """Refresh statuses one device at a time off the UI thread."""
        refreshed_count = 0
        for ip, mac in devices_to_refresh:
            status_text = self.get_device_status_text(ip)
            self.device_status_resolved.emit(ip, mac, status_text)
            refreshed_count += 1
        self.device_status_refresh_finished.emit(refreshed_count)

    def _apply_resolved_device_status(self, ip, mac, status_text):
        """Apply one resolved status update to all matching rows."""
        self.save_device_status(ip, mac, status_text)

        item = self.device_items.get(ip)
        if item is not None:
            is_favorite = self.is_favorited_device(ip, item.text(4))
            item.setText(0, status_text)
            self._style_device_item(item, is_favorite, status_text)

        for index in range(self.favorites_tree.topLevelItemCount()):
            favorite_item = self.favorites_tree.topLevelItem(index)
            if favorite_item.text(2) == ip:
                favorite_item.setText(0, status_text)
                self._style_device_item(favorite_item, True, status_text)

        self.apply_filter()

    def _finish_status_refresh(self, refreshed_count):
        """Re-enable the refresh button after the sequential status pass."""
        self.is_refreshing_status = False
        self.refresh_status_btn.setEnabled(True)
        self.apply_filter()
        self.update_status(f'Refreshed status for {refreshed_count} devices')

    def refresh_results_tree_favorites(self):
        """Update result rows to reflect current favorite status."""
        for ip, item in self.device_items.items():
            is_favorite = self.is_favorited_device(ip, item.text(4))
            item.setText(0, "★" if is_favorite else "●")

            for column in range(5):
                item.setForeground(
                    column,
                    QColor(200, 130, 0) if is_favorite else QColor(0, 100, 200)
                )

    def load_favorites(self):
        """Load favorites from local SQLite storage."""
        self.favorites = {}
        try:
            with self._db_connect() as conn:
                rows = conn.execute(
                    "SELECT favorite_key, ip, name, manufacturer, mac FROM favorites"
                ).fetchall()
            for favorite_key, ip, name, manufacturer, mac in rows:
                resolved_key = self.get_favorite_key(ip, mac) or favorite_key
                self.favorites[resolved_key] = {
                    'favorite_key': resolved_key,
                    'ip': ip,
                    'name': name,
                    'manufacturer': manufacturer,
                    'mac': mac,
                }
        except Exception:
            self.favorites = {}

    def populate_favorites_tab(self):
        """Populate the favorites tab with saved favorites."""
        self.favorites_tree.clear()

        for favorite_key, device_info in self.favorites.items():
            item = QTreeWidgetItem()
            item.setText(0, "★")
            item.setText(1, device_info['name'])
            item.setText(2, device_info['ip'])
            item.setText(3, self.format_manufacturer_label(device_info['manufacturer']))
            item.setText(4, device_info['mac'])
            item.setData(0, Qt.UserRole, favorite_key)

            for i in range(5):
                item.setForeground(i, QColor(200, 130, 0))

            self.favorites_tree.addTopLevelItem(item)

    def init_ui(self):
        """Initialize a layout styled after Advanced IP Scanner."""
        self.setWindowTitle('Advanced IP Scanner')
        self.setGeometry(80, 80, 1080, 720)
        self.setMinimumSize(920, 620)
        self.setStyleSheet("""
            QMainWindow {
                background-color: #e9edf2;
            }
            QMenuBar {
                background: #ffffff;
                border-bottom: 1px solid #c6ccd4;
                padding: 2px 6px;
            }
            QMenuBar::item {
                background: transparent;
                padding: 4px 10px;
                color: #1e1e1e;
            }
            QMenuBar::item:selected {
                background: #dbe8f6;
            }
            QStatusBar {
                background: #f7f9fb;
                border-top: 1px solid #c8cfd8;
            }
            QFrame#TopPanel, QFrame#FilterPanel, QFrame#ResultsPanel {
                background: #ffffff;
                border: 1px solid #c8cfd8;
            }
            QFrame#TopPanel {
                padding: 10px;
            }
            QFrame#FilterPanel {
                padding: 8px 10px;
            }
            QPushButton#ScanButton {
                background-color: #54c95e;
                color: white;
                border: 1px solid #46ac4f;
                border-radius: 4px;
                font-size: 25px;
                font-weight: bold;
                text-align: left;
                padding: 12px 22px;
                min-width: 148px;
                min-height: 52px;
            }
            QPushButton#ScanButton:hover {
                background-color: #49ba53;
            }
            QPushButton#PauseButton {
                background: #eceff3;
                color: #5c6572;
                border: 1px solid #cad1d9;
                border-radius: 4px;
                font-size: 24px;
                font-weight: bold;
                min-width: 68px;
                min-height: 52px;
            }
            QToolButton#ToolGlyph {
                background: transparent;
                border: 1px solid transparent;
                border-radius: 4px;
                color: #2d7bd8;
                font-size: 28px;
                min-width: 42px;
                min-height: 42px;
                padding: 4px;
            }
            QToolButton#ToolGlyph:hover {
                background: #eef5fd;
                border-color: #c7d7eb;
            }
            QLineEdit {
                background: #ffffff;
                border: 1px solid #bec7d1;
                border-radius: 3px;
                padding: 7px 10px;
                selection-background-color: #b8d7ff;
                font-size: 14px;
            }
            QLabel#HintLabel {
                color: #8a94a3;
                font-style: italic;
                font-size: 13px;
            }
            QLabel#StatusLabel {
                color: #506070;
                font-size: 13px;
            }
            QTabWidget::pane {
                border: 1px solid #c8cfd8;
                top: -1px;
                background: #ffffff;
            }
            QTabBar::tab {
                background: #eef1f5;
                border: 1px solid #c8cfd8;
                padding: 7px 18px;
                margin-right: 2px;
                color: #25303c;
            }
            QTabBar::tab:selected {
                background: #ffffff;
                border-bottom-color: #ffffff;
            }
            QTreeWidget {
                background: #ffffff;
                border: none;
                alternate-background-color: #f8fbff;
                outline: 0;
                font-size: 13px;
            }
            QTreeWidget::item {
                padding: 4px 3px;
            }
            QTreeWidget::item:selected {
                background: #d7ebff;
                color: #1c1c1c;
            }
            QHeaderView::section {
                background: #ffffff;
                border: none;
                border-bottom: 1px solid #d6dde6;
                border-right: 1px solid #edf1f5;
                padding: 8px 10px;
                font-size: 12px;
                font-weight: bold;
                color: #394552;
            }
            QProgressBar {
                border: 1px solid #b7c0cb;
                border-radius: 3px;
                background: #f4f6f8;
                text-align: center;
                min-height: 18px;
            }
            QProgressBar::chunk {
                background-color: #5cb85c;
            }
        """)

        menubar = self.menuBar()
        menubar.clear()
        menubar.setVisible(False)

        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(12, 10, 12, 10)
        main_layout.setSpacing(10)

        top_panel = QFrame()
        top_panel.setObjectName('TopPanel')
        top_layout = QHBoxLayout(top_panel)
        top_layout.setContentsMargins(10, 10, 10, 10)
        top_layout.setSpacing(10)

        self.scan_btn = QPushButton('▶ Scan')
        self.scan_btn.setObjectName('ScanButton')
        self.scan_btn.clicked.connect(self.start_scan)
        top_layout.addWidget(self.scan_btn)

        top_layout.addStretch()
        main_layout.addWidget(top_panel)

        filter_panel = QFrame()
        filter_panel.setObjectName('FilterPanel')
        filter_layout = QHBoxLayout(filter_panel)
        filter_layout.setContentsMargins(10, 8, 10, 8)
        filter_layout.setSpacing(8)

        example_label = QLabel('Scans your detected local network automatically')
        example_label.setObjectName('HintLabel')
        filter_layout.addWidget(example_label, 3)

        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText('Search devices')
        self.search_input.setClearButtonEnabled(True)
        self.search_input.textChanged.connect(self.apply_filter)
        filter_layout.addWidget(self.search_input, 2)
        main_layout.addWidget(filter_panel)

        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        main_layout.addWidget(self.progress_bar)

        self.tabs = QTabWidget()

        results_tab = QWidget()
        results_layout = QVBoxLayout(results_tab)
        results_layout.setContentsMargins(0, 0, 0, 0)
        self.tree = self._create_device_tree()
        self.tree.customContextMenuRequested.connect(self.show_context_menu)
        results_layout.addWidget(self.tree)
        self.tabs.addTab(results_tab, 'Results')

        favorites_tab = QWidget()
        favorites_layout = QVBoxLayout(favorites_tab)
        favorites_layout.setContentsMargins(0, 0, 0, 0)
        self.favorites_tree = self._create_device_tree()
        self.favorites_tree.customContextMenuRequested.connect(self.show_favorites_context_menu)
        favorites_layout.addWidget(self.favorites_tree)
        self.tabs.addTab(favorites_tab, 'Favorites')
        self.tabs.currentChanged.connect(lambda _: self.apply_filter())

        results_panel = QFrame()
        results_panel.setObjectName('ResultsPanel')
        results_wrapper = QVBoxLayout(results_panel)
        results_wrapper.setContentsMargins(0, 0, 0, 0)
        results_wrapper.addWidget(self.tabs)
        main_layout.addWidget(results_panel, 1)

        footer_layout = QHBoxLayout()
        footer_layout.setContentsMargins(2, 0, 2, 0)
        self.status_label = QLabel('Ready')
        self.status_label.setObjectName('StatusLabel')
        self.count_label = QLabel('0 alive, 0 dead, 0 unknown')
        self.count_label.setObjectName('StatusLabel')
        footer_layout.addWidget(self.status_label)
        footer_layout.addStretch()
        footer_layout.addWidget(self.count_label)
        main_layout.addLayout(footer_layout)

        self.statusBar().showMessage('Ready to scan')

    def _make_toolbar_glyph(self, text):
        """Create a simple toolbar glyph button for the scanner chrome."""
        button = QToolButton()
        button.setObjectName('ToolGlyph')
        button.setText(text)
        button.setEnabled(False)
        return button

    def _create_device_tree(self):
        """Create a tree widget with scanner-style columns."""
        tree = QTreeWidget()
        tree.setColumnCount(5)
        tree.setHeaderLabels(['Status', 'Name', 'IP', 'Manufacturer', 'MAC address'])
        tree.setAlternatingRowColors(True)
        tree.setRootIsDecorated(True)
        tree.setUniformRowHeights(False)
        tree.setIndentation(20)
        tree.setContextMenuPolicy(Qt.CustomContextMenu)
        tree.setSelectionMode(QAbstractItemView.SingleSelection)
        tree.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)
        tree.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)

        header = tree.header()
        header.setStretchLastSection(False)
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.Stretch)
        header.setSectionResizeMode(2, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(3, QHeaderView.Stretch)
        header.setSectionResizeMode(4, QHeaderView.ResizeToContents)

        return tree

    def get_device_status_text(self, ip):
        """Return Online or Offline based on a quick ping check."""
        clean_ip = (ip or '').strip()
        if not clean_ip:
            return 'Offline'

        try:
            result = subprocess.run(
                ['ping', '-n', '1', '-w', str(self.scanner.ping_timeout_ms), clean_ip],
                capture_output=True,
                timeout=max(0.2, self.scanner.process_timeout_sec)
            )
            return 'Online' if result.returncode == 0 else 'Offline'
        except Exception:
            return 'Offline'

    def resolve_status_for_device(self, device):
        """Prefer provided or cached status before falling back to a live ping."""
        ip = device.get('ip', '')
        mac = device.get('mac', '')
        status_text = (device.get('status') or '').strip()
        if status_text:
            return status_text
        return self.get_cached_device_status(ip, mac)

    def apply_filter(self):
        """Filter both trees by the search box."""
        query = ''
        if hasattr(self, 'search_input') and self.search_input is not None:
            query = self.search_input.text().strip().lower()

        self._apply_filter_to_tree(getattr(self, 'tree', None), query)
        self._apply_filter_to_tree(getattr(self, 'favorites_tree', None), query)

    def _apply_filter_to_tree(self, tree, query):
        """Hide tree rows that do not match the current query."""
        if tree is None:
            return

        for index in range(tree.topLevelItemCount()):
            item = tree.topLevelItem(index)
            visible = self._item_matches_filter(item, query)
            item.setHidden(not visible)

    def _item_matches_filter(self, item, query):
        """Return True when an item or its children match the query."""
        if item.parent() is None:
            manufacturer_filter = getattr(self, 'manufacturer_filter_text', '')
            named_only_filter = getattr(self, 'named_only_filter', False)
            manufacturer_text = item.text(3).lower()

            if manufacturer_filter and manufacturer_filter not in manufacturer_text:
                return False
            if named_only_filter and not self.item_has_display_name(item):
                return False

        if not query:
            for child_index in range(item.childCount()):
                item.child(child_index).setHidden(False)
            return True

        haystack = ' '.join(item.text(column).lower() for column in range(item.columnCount()))
        item_matches = query in haystack
        child_matches = False

        for child_index in range(item.childCount()):
            child = item.child(child_index)
            child_visible = self._item_matches_filter(child, query)
            child.setHidden(not child_visible)
            child_matches = child_matches or child_visible

        return item_matches or child_matches

    def sort_device_tree(self, tree):
        """Sort named devices before unnamed ones, then by visible label."""
        if tree is None:
            return

        items = []
        while tree.topLevelItemCount() > 0:
            items.append(tree.takeTopLevelItem(0))

        items.sort(
            key=lambda item: (
                0 if self.item_has_display_name(item) else 1,
                item.text(1).lower(),
                item.text(2),
            )
        )

        for item in items:
            tree.addTopLevelItem(item)

    def detect_local_scan_ranges(self):
        """Detect all sensible local IPv4 network ranges for scanning."""
        ranges = []
        seen = set()

        def add_range(cidr_text):
            if not cidr_text or cidr_text in seen:
                return
            seen.add(cidr_text)
            ranges.append(cidr_text)

        try:
            output = subprocess.check_output(
                ['ipconfig'],
                text=True,
                encoding='utf-8',
                errors='ignore',
                timeout=2
            )
            ipv4_address = None
            subnet_mask = None

            for raw_line in output.splitlines():
                line = raw_line.strip()
                if not line:
                    if ipv4_address and subnet_mask:
                        try:
                            network = IPv4Network(f'{ipv4_address}/{subnet_mask}', strict=False)
                            add_range(str(network))
                        except Exception:
                            pass
                    ipv4_address = None
                    subnet_mask = None
                    continue

                if 'IPv4 Address' in line or 'Autoconfiguration IPv4 Address' in line:
                    match = re.search(r'(\d{1,3}(?:\.\d{1,3}){3})', line)
                    if match:
                        candidate = match.group(1)
                        if not candidate.startswith('169.254.'):
                            ipv4_address = candidate
                elif 'Subnet Mask' in line:
                    match = re.search(r'(\d{1,3}(?:\.\d{1,3}){3})', line)
                    if match:
                        subnet_mask = match.group(1)

            if ipv4_address and subnet_mask:
                try:
                    network = IPv4Network(f'{ipv4_address}/{subnet_mask}', strict=False)
                    add_range(str(network))
                except Exception:
                    pass
        except Exception:
            pass

        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
                sock.connect(('8.8.8.8', 80))
                ipv4_address = sock.getsockname()[0]
            finally:
                sock.close()

            if ipv4_address and not ipv4_address.startswith('127.'):
                octets = ipv4_address.split('.')
                if len(octets) == 4:
                    add_range(f'{octets[0]}.{octets[1]}.{octets[2]}.0/24')
        except Exception:
            pass

        return ranges

    def start_scan(self):
        """Start network scan."""
        ip_ranges = self.detect_local_scan_ranges()
        if not ip_ranges:
            self.update_status("Couldn't detect a local network to scan")
            return

        self.tree.clear()
        self.device_items = {}
        self.scanner.alive_count = 0
        self.scanner.dead_count = 0
        self.scanner.scanned_count = 0
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)
        self.progress_bar.setFormat("Starting scan...")
        self.scan_btn.setEnabled(False)
        self.scan_btn.setText("Scanning...")
        self.is_scanning = True

        range_summary = ', '.join(ip_ranges[:3])
        if len(ip_ranges) > 3:
            range_summary += f' +{len(ip_ranges) - 3} more'
        self.update_status(f"Scanning {range_summary}...")
        self.count_label.setText("0 alive, 0 dead, 0 unknown")

        ips = []
        seen_ips = set()
        for ip_range in ip_ranges:
            for ip in self.scanner.parse_ip_range(ip_range):
                if ip not in seen_ips:
                    seen_ips.add(ip)
                    ips.append(ip)
        scan_thread = threading.Thread(target=self._run_scan, args=(ips,))
        scan_thread.daemon = True
        scan_thread.start()

    def scan_finished(self):
        """Called when scan is complete."""
        self.is_scanning = False
        self.progress_bar.setFormat("100% - Scan complete")
        self.progress_bar.setValue(100)
        self.scan_btn.setEnabled(True)
        self.scan_btn.setText("Scan")
        self.update_status(f'Scan complete - Found {self.scanner.alive_count} devices')
        self.update_device_count(self.scanner.alive_count, self.scanner.dead_count, 0)
        self.apply_filter()

    def update_status(self, message):
        """Update status message."""
        self.status_label.setText(message)
        self.statusBar().showMessage(message)

    def update_device_count(self, alive, dead, unknown):
        """Update device count display."""
        self.count_label.setText(f'{alive} alive, {dead} dead, {unknown} unknown')

    def update_progress(self, current, total):
        """Update progress bar."""
        if total <= 0:
            return

        percentage = int((current / total) * 100)
        self.progress_bar.setValue(percentage)
        self.progress_bar.setFormat(f"Scanning: {current}/{total} IPs ({percentage}%)")

        if self.is_scanning:
            self.count_label.setText(
                f'{self.scanner.alive_count} alive, '
                f'{self.scanner.dead_count} dead, '
                f'{total - current} remaining'
            )

    def add_device_to_tree(self, device):
        """Add a discovered device using scanner-like row styling."""
        item = QTreeWidgetItem()
        is_favorite = self.is_favorited_device(device['ip'], device['mac'])

        item.setText(0, "★" if is_favorite else "PC")
        item.setText(1, device['name'])
        item.setText(2, device['ip'])
        item.setText(3, self.format_manufacturer_label(device['manufacturer']))
        item.setText(4, device['mac'])

        self._style_device_item(item, is_favorite)

        if is_favorite:
            self.refresh_favorite_from_device(device)

        self.tree.addTopLevelItem(item)
        self.device_items[device['ip']] = item
        self.apply_filter()

    def add_resource_to_tree(self, ip, resource_type, resource_name):
        """Add resource details under a scanned device."""
        if ip not in self.device_items:
            return

        device_item = self.device_items[ip]
        resource_group = None
        for index in range(device_item.childCount()):
            child = device_item.child(index)
            if child.text(1) == resource_type:
                resource_group = child
                break

        if resource_group is None:
            resource_group = QTreeWidgetItem(device_item)
            resource_group.setText(0, "↳")
            resource_group.setText(1, resource_type)
            for column in range(5):
                resource_group.setForeground(column, QColor(126, 98, 34))
            resource_group.setExpanded(True)

        resource_item = QTreeWidgetItem(resource_group)
        resource_item.setText(0, "•")
        resource_item.setText(1, resource_name)
        for column in range(5):
            resource_item.setForeground(column, QColor(94, 102, 112))

        device_item.setExpanded(True)
        resource_group.setExpanded(True)
        self.apply_filter()

    def _style_device_item(self, item, is_favorite, status_text='Online'):
        """Apply colors and typography to a device row."""
        if status_text == 'Online':
            status_color = QColor(46, 125, 50)
        elif status_text == 'Loading':
            status_color = QColor(45, 123, 216)
        else:
            status_color = QColor(183, 28, 28)
        favorite_color = QColor(183, 132, 18)
        text_color = QColor(31, 34, 38)

        item.setForeground(0, status_color)
        item.setForeground(1, favorite_color if is_favorite else text_color)
        for column in range(2, 5):
            item.setForeground(column, text_color)

        item.setFont(0, QFont('Segoe UI', 9, QFont.Bold))
        item.setFont(1, QFont('Segoe UI', 10, QFont.Bold if is_favorite else QFont.Normal))

    def refresh_results_tree_favorites(self):
        """Update results rows to match favorite state."""
        for ip, item in self.device_items.items():
            is_favorite = self.is_favorited_device(ip, item.text(4))
            status_text = self.get_cached_device_status(ip, item.text(4))
            item.setText(0, status_text)
            self._style_device_item(item, is_favorite, status_text)

    def populate_favorites_tab(self):
        """Populate the favorites tab with saved favorites."""
        self.favorites_tree.clear()

        for favorite_key, device_info in self.favorites.items():
            item = QTreeWidgetItem()
            item.setText(0, "★")
            item.setText(1, device_info['name'])
            item.setText(2, device_info['ip'])
            item.setText(3, self.format_manufacturer_label(device_info['manufacturer']))
            item.setText(4, device_info['mac'])
            item.setData(0, Qt.UserRole, favorite_key)

            self._style_device_item(item, True)
            self.favorites_tree.addTopLevelItem(item)

        self.apply_filter()

    def init_ui(self):
        """Initialize a layout styled after Advanced IP Scanner."""
        self.manufacturer_filter_text = ''
        self.named_only_filter = bool(self.settings.get('named_only_default', False))

        self.setWindowTitle('Advanced IP Scanner')
        self.setGeometry(80, 80, 1080, 720)
        self.setMinimumSize(920, 620)
        self.setStyleSheet("""
            QMainWindow {
                background-color: #e9edf2;
            }
            QMenuBar {
                background: #ffffff;
                border-bottom: 1px solid #c6ccd4;
                padding: 2px 6px;
            }
            QMenuBar::item {
                background: transparent;
                padding: 4px 10px;
                color: #1e1e1e;
            }
            QMenuBar::item:selected {
                background: #dbe8f6;
            }
            QStatusBar {
                background: #f7f9fb;
                border-top: 1px solid #c8cfd8;
            }
            QFrame#TopPanel, QFrame#FilterPanel, QFrame#ResultsPanel {
                background: #ffffff;
                border: 1px solid #c8cfd8;
            }
            QFrame#TopPanel {
                padding: 10px;
            }
            QFrame#FilterPanel {
                padding: 8px 10px;
            }
            QPushButton#ScanButton {
                background-color: #54c95e;
                color: white;
                border: 1px solid #46ac4f;
                border-radius: 4px;
                font-size: 25px;
                font-weight: bold;
                text-align: left;
                padding: 12px 22px;
                min-width: 148px;
                min-height: 52px;
            }
            QPushButton#ScanButton:hover {
                background-color: #49ba53;
            }
            QPushButton#PauseButton {
                background: #eceff3;
                color: #5c6572;
                border: 1px solid #cad1d9;
                border-radius: 4px;
                font-size: 24px;
                font-weight: bold;
                min-width: 68px;
                min-height: 52px;
            }
            QToolButton#ToolGlyph {
                background: transparent;
                border: 1px solid transparent;
                border-radius: 4px;
                color: #2d7bd8;
                font-size: 28px;
                min-width: 42px;
                min-height: 42px;
                padding: 4px;
            }
            QToolButton#ToolGlyph:hover {
                background: #eef5fd;
                border-color: #c7d7eb;
            }
            QToolButton#FilterButton {
                background: #eef2f7;
                border: 1px solid #c8d0da;
                border-radius: 3px;
                color: #314050;
                padding: 6px 12px;
                font-size: 13px;
                min-width: 74px;
            }
            QToolButton#FilterButton:hover {
                background: #e4ebf3;
            }
            QPushButton#SettingsButton {
                background: #eef2f7;
                border: 1px solid #c8d0da;
                border-radius: 3px;
                color: #314050;
                padding: 7px 12px;
                font-size: 13px;
            }
            QPushButton#SettingsButton:hover {
                background: #e4ebf3;
            }
            QLineEdit {
                background: #ffffff;
                border: 1px solid #bec7d1;
                border-radius: 3px;
                padding: 7px 10px;
                selection-background-color: #b8d7ff;
                font-size: 14px;
            }
            QLabel#HintLabel {
                color: #8a94a3;
                font-style: italic;
                font-size: 13px;
            }
            QLabel#StatusLabel {
                color: #506070;
                font-size: 13px;
            }
            QTabWidget::pane {
                border: 1px solid #c8cfd8;
                top: -1px;
                background: #ffffff;
            }
            QTabBar::tab {
                background: #eef1f5;
                border: 1px solid #c8cfd8;
                padding: 7px 18px;
                margin-right: 2px;
                color: #25303c;
            }
            QTabBar::tab:selected {
                background: #ffffff;
                border-bottom-color: #ffffff;
            }
            QTreeWidget {
                background: #ffffff;
                border: none;
                alternate-background-color: #f8fbff;
                outline: 0;
                font-size: 13px;
            }
            QTreeWidget::item {
                padding: 4px 3px;
            }
            QTreeWidget::item:selected {
                background: #d7ebff;
                color: #1c1c1c;
            }
            QHeaderView::section {
                background: #ffffff;
                border: none;
                border-bottom: 1px solid #d6dde6;
                border-right: 1px solid #edf1f5;
                padding: 8px 10px;
                font-size: 12px;
                font-weight: bold;
                color: #394552;
            }
            QProgressBar {
                border: 1px solid #b7c0cb;
                border-radius: 3px;
                background: #f4f6f8;
                text-align: center;
                min-height: 18px;
            }
            QProgressBar::chunk {
                background-color: #5cb85c;
            }
        """)

        menubar = self.menuBar()
        menubar.clear()
        menubar.setVisible(False)

        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(12, 10, 12, 10)
        main_layout.setSpacing(10)

        top_panel = QFrame()
        top_panel.setObjectName('TopPanel')
        top_layout = QHBoxLayout(top_panel)
        top_layout.setContentsMargins(10, 10, 10, 10)
        top_layout.setSpacing(10)

        self.scan_btn = QPushButton('Scan')
        self.scan_btn.setObjectName('ScanButton')
        self.scan_btn.clicked.connect(self.start_scan)
        top_layout.addWidget(self.scan_btn)

        self.refresh_status_btn = QPushButton('Refresh Status')
        self.refresh_status_btn.setObjectName('SettingsButton')
        self.refresh_status_btn.clicked.connect(self.refresh_all_statuses)
        top_layout.addWidget(self.refresh_status_btn)

        top_layout.addStretch()
        main_layout.addWidget(top_panel)

        filter_panel = QFrame()
        filter_panel.setObjectName('FilterPanel')
        filter_layout = QHBoxLayout(filter_panel)
        filter_layout.setContentsMargins(10, 8, 10, 8)
        filter_layout.setSpacing(8)

        example_label = QLabel('Scans your detected local network automatically')
        example_label.setObjectName('HintLabel')
        filter_layout.addWidget(example_label, 3)

        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText('Search devices')
        self.search_input.setClearButtonEnabled(True)
        self.search_input.textChanged.connect(self.apply_filter)
        filter_layout.addWidget(self.search_input, 2)

        self.filter_button = QToolButton()
        self.filter_button.setObjectName('FilterButton')
        self.filter_button.setText('Filter ▾')
        self.filter_button.setPopupMode(QToolButton.InstantPopup)
        self.filter_button.setMenu(self._build_filter_menu())
        filter_layout.addWidget(self.filter_button)

        self.settings_button = QPushButton('Settings')
        self.settings_button.setObjectName('SettingsButton')
        self.settings_button.clicked.connect(self.open_settings_dialog)
        filter_layout.addWidget(self.settings_button)
        main_layout.addWidget(filter_panel)

        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        main_layout.addWidget(self.progress_bar)

        self.tabs = QTabWidget()

        results_tab = QWidget()
        results_layout = QVBoxLayout(results_tab)
        results_layout.setContentsMargins(0, 0, 0, 0)
        self.tree = self._create_device_tree()
        self.tree.customContextMenuRequested.connect(self.show_context_menu)
        results_layout.addWidget(self.tree)
        self.tabs.addTab(results_tab, 'Results')

        favorites_tab = QWidget()
        favorites_layout = QVBoxLayout(favorites_tab)
        favorites_layout.setContentsMargins(0, 0, 0, 0)
        self.favorites_tree = self._create_device_tree()
        self.favorites_tree.customContextMenuRequested.connect(self.show_favorites_context_menu)
        favorites_layout.addWidget(self.favorites_tree)
        self.tabs.addTab(favorites_tab, 'Favorites')
        self.tabs.currentChanged.connect(lambda _: self.apply_filter())

        results_panel = QFrame()
        results_panel.setObjectName('ResultsPanel')
        results_wrapper = QVBoxLayout(results_panel)
        results_wrapper.setContentsMargins(0, 0, 0, 0)
        results_wrapper.addWidget(self.tabs)
        main_layout.addWidget(results_panel, 1)

        footer_layout = QHBoxLayout()
        footer_layout.setContentsMargins(2, 0, 2, 0)
        self.status_label = QLabel('Ready')
        self.status_label.setObjectName('StatusLabel')
        self.count_label = QLabel('0 alive, 0 dead, 0 unknown')
        self.count_label.setObjectName('StatusLabel')
        footer_layout.addWidget(self.status_label)
        footer_layout.addStretch()
        footer_layout.addWidget(self.count_label)
        main_layout.addLayout(footer_layout)

        self.statusBar().showMessage('Ready to scan')
        self.update_filter_button_text()

    def _build_filter_menu(self):
        """Create the popup filter menu."""
        self.filter_menu = QMenu(self)

        filter_widget = QWidget()
        layout = QVBoxLayout(filter_widget)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        manufacturer_label = QLabel('Manufacturer contains')
        layout.addWidget(manufacturer_label)

        self.manufacturer_filter_input = QLineEdit()
        self.manufacturer_filter_input.setPlaceholderText('e.g. Hewlett Packard')
        self.manufacturer_filter_input.setText(self.manufacturer_filter_text)
        self.manufacturer_filter_input.textChanged.connect(self.apply_filter_menu)
        layout.addWidget(self.manufacturer_filter_input)

        self.named_only_checkbox = QCheckBox('Only show PCs where a name was found')
        self.named_only_checkbox.setChecked(self.named_only_filter)
        self.named_only_checkbox.stateChanged.connect(lambda _: self.apply_filter_menu())
        layout.addWidget(self.named_only_checkbox)

        action = QWidgetAction(self.filter_menu)
        action.setDefaultWidget(filter_widget)
        self.filter_menu.addAction(action)
        return self.filter_menu

    def apply_filter_menu(self):
        """Apply the popup filter settings immediately."""
        self.manufacturer_filter_text = self.manufacturer_filter_input.text().strip().lower()
        self.named_only_filter = self.named_only_checkbox.isChecked()
        self.update_filter_button_text()
        self.apply_filter()

    def update_filter_button_text(self):
        """Reflect whether extra filters are active."""
        if not hasattr(self, 'filter_button') or self.filter_button is None:
            return

        if self.manufacturer_filter_text or self.named_only_filter:
            self.filter_button.setText('Filter •')
        else:
            self.filter_button.setText('Filter ▾')

    def open_settings_dialog(self):
        """Open a settings window for scan behavior and defaults."""
        dialog = QDialog(self)
        dialog.setWindowTitle('Settings')
        dialog.setModal(True)
        dialog.resize(420, 0)

        layout = QVBoxLayout(dialog)
        form = QFormLayout()
        form.setSpacing(10)

        named_only_default_checkbox = QCheckBox('Enable by default')
        named_only_default_checkbox.setChecked(bool(self.settings.get('named_only_default', False)))

        max_workers_spin = QSpinBox()
        max_workers_spin.setRange(16, 1024)
        max_workers_spin.setValue(int(self.settings.get('max_workers', self.scanner.max_workers)))

        detail_workers_spin = QSpinBox()
        detail_workers_spin.setRange(4, 256)
        detail_workers_spin.setValue(int(self.settings.get('detail_workers', self.scanner.detail_workers)))

        resource_workers_spin = QSpinBox()
        resource_workers_spin.setRange(2, 256)
        resource_workers_spin.setValue(int(self.settings.get('resource_workers', self.scanner.resource_workers)))

        ping_timeout_spin = QSpinBox()
        ping_timeout_spin.setRange(50, 5000)
        ping_timeout_spin.setSuffix(' ms')
        ping_timeout_spin.setValue(int(self.settings.get('ping_timeout_ms', self.scanner.ping_timeout_ms)))

        process_timeout_spin = QDoubleSpinBox()
        process_timeout_spin.setRange(0.1, 10.0)
        process_timeout_spin.setSingleStep(0.1)
        process_timeout_spin.setSuffix(' s')
        process_timeout_spin.setDecimals(1)
        process_timeout_spin.setValue(float(self.settings.get('process_timeout_sec', self.scanner.process_timeout_sec)))

        form.addRow('Named-only filter', named_only_default_checkbox)
        form.addRow('Fast scan threads', max_workers_spin)
        form.addRow('Detail lookup threads', detail_workers_spin)
        form.addRow('Resource lookup threads', resource_workers_spin)
        form.addRow('Ping timeout', ping_timeout_spin)
        form.addRow('Process timeout', process_timeout_spin)
        layout.addLayout(form)

        hint_label = QLabel(
            'Higher thread counts scan faster but can be noisier. '
            'Lower timeouts are faster but may miss slower devices.'
        )
        hint_label.setWordWrap(True)
        layout.addWidget(hint_label)

        if self.is_scanning:
            live_note = QLabel('A scan is running. Saved changes will apply immediately where possible.')
            live_note.setWordWrap(True)
            layout.addWidget(live_note)

        button_box = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        layout.addWidget(button_box)

        def save_and_close():
            self.settings.update({
                'named_only_default': named_only_default_checkbox.isChecked(),
                'max_workers': max_workers_spin.value(),
                'detail_workers': detail_workers_spin.value(),
                'resource_workers': resource_workers_spin.value(),
                'ping_timeout_ms': ping_timeout_spin.value(),
                'process_timeout_sec': process_timeout_spin.value(),
            })

            self.scanner.apply_runtime_settings(
                max_workers=self.settings['max_workers'],
                detail_workers=self.settings['detail_workers'],
                resource_workers=self.settings['resource_workers'],
                ping_timeout_ms=self.settings['ping_timeout_ms'],
                process_timeout_sec=self.settings['process_timeout_sec'],
            )
            self.save_settings()

            self.named_only_filter = bool(self.settings.get('named_only_default', False))
            if hasattr(self, 'named_only_checkbox'):
                self.named_only_checkbox.setChecked(self.named_only_filter)
            self.update_filter_button_text()
            self.apply_filter()
            self.update_status('Settings saved')
            dialog.accept()

        button_box.accepted.connect(save_and_close)
        button_box.rejected.connect(dialog.reject)
        dialog.exec_()

    def add_device_to_tree(self, device):
        """Add a discovered device using a combined name/IP label."""
        item = self.device_items.get(device['ip'])
        is_new_item = item is None
        if is_new_item:
            item = QTreeWidgetItem()
        is_favorite = self.is_favorited_device(device['ip'], device['mac'])
        status_text = self.resolve_status_for_device(device)
        display_name = self.get_display_name(device['name'], device['ip'], device['mac'])
        nickname = self.get_device_nickname(device['ip'], device['mac'])

        item.setText(0, status_text)
        item.setText(1, self.format_device_label(display_name, device['ip']))
        item.setText(2, device['ip'])
        item.setText(3, self.format_manufacturer_label(device['manufacturer']))
        item.setText(4, device['mac'])
        item.setData(1, Qt.UserRole, device['name'])
        item.setData(1, Qt.UserRole + 1, nickname)
        self.save_device_status(device['ip'], device['mac'], status_text)

        self._style_device_item(item, is_favorite, status_text)

        if is_favorite:
            self.refresh_favorite_from_device(device)

        if is_new_item:
            self.tree.addTopLevelItem(item)
        self.device_items[device['ip']] = item
        self.sort_device_tree(self.tree)
        self.apply_filter()

    def populate_favorites_tab(self):
        """Populate the favorites tab with saved favorites."""
        self.favorites_tree.clear()

        for favorite_key, device_info in self.favorites.items():
            item = QTreeWidgetItem()
            status_text = self.get_cached_device_status(device_info['ip'], device_info['mac'])
            display_name = self.get_display_name(
                device_info.get('name', ''),
                device_info['ip'],
                device_info['mac']
            )
            nickname = self.get_device_nickname(device_info['ip'], device_info['mac'])
            item.setText(0, status_text)
            item.setText(1, self.format_device_label(display_name, device_info['ip']))
            item.setText(2, device_info['ip'])
            item.setText(3, self.format_manufacturer_label(device_info['manufacturer']))
            item.setText(4, device_info['mac'])
            item.setData(0, Qt.UserRole, favorite_key)
            item.setData(1, Qt.UserRole, device_info.get('name', ''))
            item.setData(1, Qt.UserRole + 1, nickname)

            self._style_device_item(item, True, status_text)
            self.favorites_tree.addTopLevelItem(item)

        self.sort_device_tree(self.favorites_tree)
        self.apply_filter()


def main():
    app = QApplication(sys.argv)
    window = NetworkDiscoveryApp()
    window.show()
    sys.exit(app.exec_())


if __name__ == '__main__':
    main()
