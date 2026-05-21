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
    "00:00:0C": "Cisco",
    "00:00:39": "Toshiba",
    "00:00:4C": "NEC",
    "00:00:85": "Canon",
    "00:00:88": "Brocade",
    "00:00:97": "Dell EMC",
    "00:00:AA": "Xerox",
    "00:00:B4": "Edimax",
    "00:00:C5": "ARRIS",
    "00:00:CA": "ARRIS",
    "00:00:E2": "Acer",
    "00:00:F0": "Samsung",
    "00:01:02": "3Com",
    "00:01:03": "3Com",
    "00:01:0F": "Brocade",
    "00:01:24": "Acer",
    "00:01:42": "Cisco",
    "00:01:43": "Cisco",
    "00:01:44": "Dell EMC",
    "00:01:4A": "Sony",
    "00:01:5D": "Oracle",
    "00:01:63": "Cisco",
    "00:01:64": "Cisco",
    "00:01:6C": "Foxconn",
    "00:01:96": "Cisco",
    "00:01:97": "Cisco",
    "00:01:C7": "Cisco",
    "00:01:C9": "Cisco",
    "00:01:E3": "Siemens",
    "00:01:E6": "Hewlett Packard",
    "00:01:E7": "Hewlett Packard",
    "00:02:16": "Cisco",
    "00:02:17": "Cisco",
    "00:03:6B": "Cisco",
    "00:03:93": "Apple",
    "00:03:FF": "Microsoft",
    "00:04:20": "Samsung",
    "00:04:23": "Intel",
    "00:04:25": "Atmel",
    "00:04:5A": "Cisco",
    "00:04:76": "3Com",
    "00:04:E2": "SMC Networks",
    "00:04:ED": "Billion Electric",
    "00:05:02": "Apple",
    "00:05:5D": "D-Link",
    "00:05:69": "VMware",
    "00:05:9A": "Cisco",
    "00:05:AD": "Topspin Communications",
    "00:05:BD": "Roax",
    "00:05:DC": "Cisco",
    "00:06:25": "The Linksys Group",
    "00:06:5B": "Dell",
    "00:06:7C": "Cisco",
    "00:06:7E": "Cisco",
    "00:06:DD": "Cisco",
    "00:07:0D": "Cisco",
    "00:07:4D": "Zyxel",
    "00:07:85": "Cisco",
    "00:07:E9": "Intel",
    "00:08:02": "Hewlett Packard",
    "00:08:20": "Cisco",
    "00:08:2F": "Cisco",
    "00:08:74": "Dell",
    "00:08:A1": "Cisco",
    "00:08:C7": "Hewlett Packard",
    "00:09:43": "Cisco",
    "00:09:6B": "IBM",
    "00:09:B6": "Cisco",
    "00:09:E8": "Cisco",
    "00:0A:27": "Apple",
    "00:0A:41": "Cisco",
    "00:0A:42": "Cisco",
    "00:0A:5E": "3Com",
    "00:0A:95": "Apple",
    "00:0B:46": "Cisco",
    "00:0B:5D": "Cisco",
    "00:0B:6B": "Wistron",
    "00:0B:86": "Cisco",
    "00:0B:CD": "Hewlett Packard",
    "00:0C:29": "VMware",
    "00:0C:41": "Cisco-Linksys",
    "00:0C:6E": "ASUSTek",
    "00:0C:76": "Apple",
    "00:0C:85": "Cisco",
    "00:0C:DB": "Hewlett Packard",
    "00:0D:56": "Dell",
    "00:0D:60": "IBM",
    "00:0D:88": "D-Link",
    "00:0D:93": "Apple",
    "00:0D:BC": "Cisco",
    "00:0D:BD": "Cisco",
    "00:0E:08": "Cisco-Linksys",
    "00:0E:35": "Intel",
    "00:0E:38": "Cisco",
    "00:0E:7F": "Hewlett Packard",
    "00:0E:A6": "ASUSTek",
    "00:0E:D7": "Cisco",
    "00:0E:E8": "Zyxel",
    "00:0F:1F": "Dell",
    "00:0F:20": "Hewlett Packard",
    "00:0F:34": "Cisco",
    "00:0F:66": "Cisco-Linksys",
    "00:0F:B5": "NETGEAR",
    "00:10:11": "Cisco",
    "00:10:18": "Broadcom",
    "00:10:5A": "3Com",
    "00:10:83": "Hewlett Packard",
    "00:10:E3": "Hewlett Packard",
    "00:11:09": "Micro-Star International",
    "00:11:11": "Intel",
    "00:11:22": "Cisco",
    "00:11:24": "Apple",
    "00:11:32": "Synology",
    "00:11:43": "Dell",
    "00:11:5C": "Cisco-Linksys",
    "00:11:85": "Hewlett Packard",
    "00:11:88": "Hewlett Packard",
    "00:11:93": "Cisco",
    "00:11:95": "Cisco",
    "00:11:D8": "ASUSTek",
    "00:12:17": "Cisco-Linksys",
    "00:12:3F": "Dell",
    "00:12:79": "Hewlett Packard",
    "00:12:7F": "Cisco",
    "00:12:80": "Cisco",
    "00:12:88": "Dell",
    "00:12:BA": "Hewlett Packard",
    "00:12:F0": "Intel",
    "00:13:02": "Intel",
    "00:13:10": "Cisco-Linksys",
    "00:13:20": "Intel",
    "00:13:46": "D-Link",
    "00:13:72": "Dell",
    "00:13:77": "Samsung",
    "00:13:A9": "Sony",
    "00:13:CE": "Intel",
    "00:14:22": "Dell",
    "00:14:38": "Hewlett Packard",
    "00:14:51": "Apple",
    "00:14:5E": "IBM",
    "00:14:69": "Cisco-Linksys",
    "00:14:85": "Hewlett Packard",
    "00:14:A4": "Hon Hai / Foxconn",
    "00:14:BF": "Cisco-Linksys",
    "00:14:C2": "Hewlett Packard",
    "00:14:D1": "TRENDnet",
    "00:15:00": "Intel",
    "00:15:17": "Intel",
    "00:15:5D": "Microsoft Hyper-V",
    "00:15:60": "Hewlett Packard",
    "00:15:99": "Samsung",
    "00:15:9B": "Cisco",
    "00:15:C5": "Dell",
    "00:15:F2": "ASUSTek",
    "00:16:17": "MSI",
    "00:16:41": "Universal Global Scientific Industrial",
    "00:16:44": "Lite-On",
    "00:16:6F": "Intel",
    "00:16:76": "Intel",
    "00:16:CB": "Apple",
    "00:16:CF": "Apple",
    "00:16:EA": "Intel",
    "00:17:08": "Hewlett Packard",
    "00:17:31": "ASUSTek",
    "00:17:88": "Philips Lighting",
    "00:17:95": "Cisco",
    "00:17:9A": "D-Link",
    "00:17:A4": "Global Data Services",
    "00:17:C5": "SonicWall",
    "00:17:F2": "Apple",
    "00:18:39": "Cisco-Linksys",
    "00:18:3A": "D-Link",
    "00:18:4D": "NETGEAR",
    "00:18:8B": "Dell",
    "00:18:8D": "Nokia",
    "00:18:DE": "Intel",
    "00:19:06": "Cisco",
    "00:19:07": "Cisco",
    "00:19:B9": "Dell",
    "00:19:D2": "Intel",
    "00:19:E3": "Apple",
    "00:1A:11": "Google",
    "00:1A:2B": "Ayecom",
    "00:1A:4B": "Hewlett Packard",
    "00:1A:6B": "Universal Global Scientific Industrial",
    "00:1A:70": "Cisco-Linksys",
    "00:1A:79": "Apple",
    "00:1A:92": "ASUSTek",
    "00:1A:A0": "Dell",
    "00:1B:11": "D-Link",
    "00:1B:21": "Intel",
    "00:1B:24": "Quanta Computer",
    "00:1B:38": "Samsung",
    "00:1B:63": "Apple",
    "00:1B:78": "Hewlett Packard",
    "00:1B:FC": "ASUSTek",
    "00:1C:10": "Cisco-Linksys",
    "00:1C:14": "VMware",
    "00:1C:23": "Dell",
    "00:1C:25": "Hon Hai / Foxconn",
    "00:1C:42": "Parallels",
    "00:1C:58": "Cisco",
    "00:1C:7B": "Google",
    "00:1C:B3": "Apple",
    "00:1D:09": "Dell",
    "00:1D:4F": "Apple",
    "00:1D:60": "ASUSTek",
    "00:1D:72": "Wistron",
    "00:1D:7E": "Cisco-Linksys",
    "00:1D:BA": "Sony",
    "00:1D:E0": "Intel",
    "00:1E:0B": "Hewlett Packard",
    "00:1E:4C": "Hon Hai / Foxconn",
    "00:1E:52": "Apple",
    "00:1E:58": "Dell",
    "00:1E:65": "Intel",
    "00:1E:68": "Quanta Computer",
    "00:1E:8C": "NETGEAR",
    "00:1E:C2": "Apple",
    "00:1E:C9": "Dell",
    "00:1F:16": "Wistron",
    "00:1F:29": "Hewlett Packard",
    "00:1F:3A": "Hon Hai / Foxconn",
    "00:1F:3B": "Cisco",
    "00:1F:5B": "Apple",
    "00:1F:C6": "ASUSTek",
    "00:1F:F3": "Apple",
    "00:21:00": "Gemtek Technology",
    "00:21:5C": "Intel",
    "00:21:6A": "Intel",
    "00:21:70": "Dell",
    "00:21:91": "D-Link",
    "00:21:9B": "Dell",
    "00:21:CC": "Cisco",
    "00:21:E9": "Apple",
    "00:22:15": "ASUSTek",
    "00:22:19": "Dell",
    "00:22:3F": "Netgear",
    "00:22:41": "Apple",
    "00:22:43": "AzureWave",
    "00:22:48": "Microsoft",
    "00:22:5F": "Lite-On",
    "00:22:64": "Hewlett Packard",
    "00:22:90": "Cisco",
    "00:22:FA": "Intel",
    "00:23:12": "Apple",
    "00:23:14": "Intel",
    "00:23:24": "G-PRO Computer",
    "00:23:4D": "Hon Hai / Foxconn",
    "00:23:54": "ASUSTek",
    "00:23:69": "Hon Hai / Foxconn",
    "00:23:6C": "Apple",
    "00:23:7D": "Hewlett Packard",
    "00:23:AE": "Dell",
    "00:23:DF": "Apple",
    "00:24:01": "D-Link",
    "00:24:81": "Hewlett Packard",
    "00:24:8C": "ASUSTek",
    "00:24:BE": "Sony",
    "00:24:D7": "Intel",
    "00:24:E8": "Dell",
    "00:25:00": "Apple",
    "00:25:11": "D-Link",
    "00:25:3C": "2Wire",
    "00:25:4B": "Apple",
    "00:25:56": "VMware",
    "00:25:64": "Dell",
    "00:25:90": "Super Micro Computer",
    "00:25:9C": "Cisco",
    "00:25:B3": "Hewlett Packard",
    "00:25:BC": "Apple",
    "00:26:08": "Apple",
    "00:26:18": "Buffalo",
    "00:26:44": "Apple",
    "00:26:55": "Hewlett Packard",
    "00:26:82": "Gemtek Technology",
    "00:26:B9": "Dell",
    "00:26:BB": "Apple",
    "00:30:48": "Super Micro Computer",
    "00:40:96": "Cisco",
    "00:50:43": "Marvell",
    "00:50:56": "VMware",
    "00:50:8B": "Compaq",
    "00:50:BA": "D-Link",
    "00:50:FC": "Edimax",
    "00:90:27": "Intel",
    "00:A0:C9": "Intel",
    "00:E0:4C": "Realtek",
    "04:0C:CE": "Apple",
    "04:15:52": "Apple",
    "04:18:D6": "Ubiquiti",
    "04:1E:64": "Apple",
    "04:26:65": "Apple",
    "04:32:01": "Samsung",
    "04:4B:ED": "Apple",
    "04:52:F3": "Apple",
    "04:54:53": "Apple",
    "04:69:F8": "Apple",
    "04:7B:CB": "Universal Global Scientific Industrial",
    "04:83:1E": "Huawei",
    "04:DB:56": "Apple",
    "04:E5:36": "Apple",
    "04:F1:3E": "Apple",
    "04:F7:E4": "Apple",
    "08:00:27": "PCS Systemtechnik",
    "08:11:96": "Intel",
    "08:3E:8E": "Hon Hai / Foxconn",
    "08:5B:0E": "Fortinet",
    "08:66:98": "Apple",
    "08:6A:0A": "ASUSTek",
    "08:70:45": "Apple",
    "08:74:02": "Apple",
    "08:7A:4C": "Huawei",
    "08:9E:01": "Quanta Computer",
    "08:CC:68": "Cisco",
    "08:D4:0C": "Intel",
    "08:EA:44": "Extreme Networks",
    "0C:21:38": "Hengstler",
    "0C:27:24": "Cisco",
    "0C:29:EF": "Dell",
    "0C:2D:E9": "Apple",
    "0C:30:21": "Apple",
    "0C:37:DC": "Huawei",
    "0C:4D:E9": "Apple",
    "0C:51:01": "Apple",
    "0C:54:15": "Intel",
    "0C:57:EB": "Mueller Systems",
    "0C:74:C2": "Apple",
    "0C:8B:FD": "Intel",
    "0C:9D:92": "Apple",
    "0C:B3:19": "Samsung",
    "0C:D2:92": "Intel",
    "0C:D7:46": "Apple",
    "0C:DA:41": "HANGZHOU HIKVISION",
    "0C:DD:24": "Apple",
    "0C:F3:EE": "EM Microelectronic",
    "10:02:B5": "Intel",
    "10:07:23": "Cisco",
    "10:0B:A9": "Intel",
    "10:1C:0C": "Apple",
    "10:40:F3": "Apple",
    "10:41:7F": "Apple",
    "10:56:CA": "Peplink",
    "10:60:4B": "Hewlett Packard",
    "10:68:3F": "LG Electronics",
    "10:78:D2": "Elitegroup Computer Systems",
    "10:9A:DD": "Apple",
    "10:BF:48": "ASUSTek",
    "10:C3:7B": "ASUSTek",
    "10:DA:43": "NETGEAR",
    "10:DD:B1": "Apple",
    "10:E7:C6": "Hewlett Packard Enterprise",
    "10:F0:05": "Intel",
    "14:10:9F": "Apple",
    "14:18:77": "Dell",
    "14:49:E0": "Samsung",
    "14:5A:05": "Apple",
    "14:7D:DA": "ASUSTek",
    "14:7D:F3": "Apple",
    "14:91:82": "Belkin",
    "14:99:E2": "Apple",
    "14:B4:84": "Samsung",
    "14:C1:4E": "Google",
    "14:CC:20": "TP-Link",
    "14:DA:E9": "ASUSTek",
    "14:F4:2A": "Samsung",
    "18:03:73": "Dell",
    "18:20:32": "Apple",
    "18:34:51": "Apple",
    "18:3D:A2": "Intel",
    "18:56:80": "Apple",
    "18:65:90": "Apple",
    "18:66:DA": "Dell",
    "18:AF:61": "Apple",
    "18:E7:F4": "Apple",
    "18:EE:69": "Apple",
    "1C:1A:C0": "Apple",
    "1C:3E:84": "Hon Hai / Foxconn",
    "1C:4B:D6": "AzureWave",
    "1C:5C:F2": "Apple",
    "1C:65:9D": "Lite-On",
    "1C:87:2C": "ASUSTek",
    "1C:91:48": "Apple",
    "1C:99:4C": "Murata Manufacturing",
    "1C:AB:A7": "Apple",
    "1C:B0:94": "Hewlett Packard",
    "1C:C1:DE": "Hewlett Packard",
    "1C:E6:2B": "Apple",
    "1C:F0:3E": "Wearhaus",
    "20:0C:C8": "NETGEAR",
    "20:1A:06": "Apple",
    "20:37:06": "Cisco",
    "20:3C:AE": "Apple",
    "20:68:9D": "Lite-On",
    "20:78:F0": "Apple",
    "20:A2:E4": "Apple",
    "20:C9:D0": "Apple",
    "20:CF:30": "ASUSTek",
    "20:EE:28": "Apple",
    "24:0A:64": "AzureWave",
    "24:18:1D": "Samsung",
    "24:24:0E": "Apple",
    "24:77:03": "Intel",
    "24:81:AA": "KSH International",
    "24:5A:4C": "Ubiquiti",
    "24:A0:74": "Apple",
    "24:A2:E1": "Apple",
    "24:A4:3C": "Ubiquiti",
    "24:AB:81": "Apple",
    "24:BE:05": "Hewlett Packard",
    "24:E3:14": "Apple",
    "24:F5:A2": "Belkin",
    "28:16:A8": "Microsoft",
    "28:18:78": "Microsoft",
    "28:37:37": "Apple",
    "28:5A:EB": "Apple",
    "28:5B:A1": "Apple",
    "28:6A:B8": "Apple",
    "28:6B:35": "Dell",
    "28:6D:CD": "Apple",
    "28:CF:DA": "Apple",
    "28:CF:E9": "Apple",
    "28:CD:C1": "Raspberry Pi",
    "28:DE:65": "Aruba / HPE",
    "28:E0:2C": "Apple",
    "28:E1:4C": "Apple",
    "28:E7:CF": "Apple",
    "28:EA:2D": "Apple",
    "28:EC:22": "eero",
    "28:EC:95": "Apple",
    "28:ED:6A": "Apple",
    "28:EE:52": "TP-Link",
    "28:EF:01": "Amazon Technologies",
    "28:F0:33": "Apple",
    "28:F0:76": "Apple",
    "28:F1:0E": "Dell",
    "2C:1F:23": "Apple",
    "2C:33:7A": "Hon Hai / Foxconn",
    "2C:41:38": "Hewlett Packard",
    "2C:54:2D": "Cisco Meraki",
    "2C:56:DC": "ASUSTek",
    "2C:59:E5": "Hewlett Packard",
    "2C:6E:85": "Intel",
    "2C:B0:5D": "NETGEAR",
    "2C:F0:A2": "Apple",
    "30:10:E4": "Apple",
    "30:35:AD": "Apple",
    "30:46:9A": "NETGEAR",
    "30:63:6B": "Apple",
    "30:85:A9": "ASUSTek",
    "30:90:AB": "Apple",
    "30:9C:23": "Hewlett Packard",
    "30:A8:DB": "Sony",
    "30:B5:C2": "TP-Link",
    "30:C1:B7": "Samsung",
    "30:D6:C9": "Samsung",
    "30:F7:C5": "Apple",
    "34:02:86": "Intel",
    "34:08:04": "D-Link",
    "34:12:98": "Apple",
    "34:15:9E": "Apple",
    "34:17:EB": "Dell",
    "34:23:87": "Hon Hai / Foxconn",
    "34:36:3B": "Apple",
    "34:51:C9": "Apple",
    "34:68:95": "Hewlett Packard",
    "34:97:F6": "ASUSTek",
    "34:A3:95": "Apple",
    "34:AB:37": "Apple",
    "34:C0:59": "Apple",
    "34:E6:AD": "Intel",
    "34:F6:4B": "Intel",
    "38:0F:4A": "Apple",
    "38:2C:4A": "ASUSTek",
    "38:48:4C": "Apple",
    "38:59:F9": "Hon Hai / Foxconn",
    "38:60:77": "PEGATRON",
    "38:6B:BB": "Apple",
    "38:71:DE": "Apple",
    "38:8A:B7": "ITC Networks",
    "38:CA:DA": "Apple",
    "38:C9:86": "Apple",
    "38:F9:D3": "Apple",
    "38:FF:36": "Ruckus Wireless",
    "3A:35:41": "Raspberry Pi",
    "3C:07:54": "Apple",
    "3C:15:C2": "Apple",
    "3C:22:FB": "Apple",
    "3C:25:D7": "Nokia",
    "3C:2E:F9": "Apple",
    "3C:52:82": "Hewlett Packard Enterprise",
    "3C:5A:B4": "Google Nest",
    "3C:7A:8A": "Apple",
    "3C:A9:F4": "Intel",
    "3C:AB:8E": "Apple",
    "3C:D0:F8": "Apple",
    "3C:E0:72": "Apple",
    "40:30:04": "Apple",
    "40:4D:7F": "Apple",
    "40:6C:8F": "Apple",
    "40:9C:28": "Apple",
    "40:A6:D9": "Apple",
    "40:B3:95": "Apple",
    "40:D3:2D": "Apple",
    "40:FC:89": "Apple",
    "44:00:10": "Apple",
    "44:2A:60": "Apple",
    "44:2C:05": "AMPAK Technology",
    "44:4C:0C": "Apple",
    "44:65:0D": "Amazon Technologies",
    "44:74:6C": "Apple",
    "44:85:00": "Intel",
    "44:91:60": "Murata Manufacturing",
    "44:D9:E7": "Ubiquiti",
    "44:FB:42": "Apple",
    "48:0F:CF": "Hewlett Packard",
    "48:43:7C": "Apple",
    "48:4B:AA": "Apple",
    "48:5A:3F": "WISOL",
    "48:60:BC": "Apple",
    "48:74:6E": "Apple",
    "48:BF:6B": "Apple",
    "48:D7:05": "Apple",
    "48:E9:F1": "Apple",
    "4C:32:75": "Apple",
    "4C:57:CA": "Apple",
    "4C:7C:5F": "Apple",
    "4C:8D:79": "Apple",
    "4C:B1:99": "Apple",
    "4C:BA:D7": "Apple",
    "4C:D7:17": "Dell",
    "4C:D9:8F": "Dell",
    "4C:DD:31": "Samsung",
    "4C:E1:73": "IEEE Registration Authority",
    "50:32:37": "Apple",
    "50:3D:E5": "Cisco Meraki",
    "50:46:5D": "ASUSTek",
    "50:56:BF": "Samsung",
    "50:65:F3": "Hewlett Packard",
    "50:82:D5": "Apple",
    "50:9E:A7": "Samsung",
    "50:A4:C8": "Samsung",
    "50:C7:BF": "TP-Link",
    "50:EA:D6": "Apple",
    "50:FC:9F": "Samsung",
    "52:54:00": "QEMU",
    "54:04:A6": "ASUSTek",
    "54:26:96": "Apple",
    "54:33:CB": "Apple",
    "54:4E:90": "Apple",
    "54:72:4F": "Apple",
    "54:9F:13": "Apple",
    "54:AE:27": "Apple",
    "54:BF:64": "Dell",
    "54:E4:3A": "Apple",
    "58:1F:28": "Apple",
    "58:55:CA": "Apple",
    "58:6D:8F": "Cisco-Linksys",
    "58:B0:35": "Apple",
    "58:E2:8F": "Apple",
    "58:F9:87": "Huawei",
    "5C:09:79": "Apple",
    "5C:51:4F": "Intel",
    "5C:59:48": "Apple",
    "5C:8D:4E": "Apple",
    "5C:96:9D": "Apple",
    "5C:97:F3": "Apple",
    "5C:F5:DA": "Apple",
    "60:03:08": "Apple",
    "60:30:D4": "Apple",
    "60:33:4B": "Apple",
    "60:57:18": "Intel",
    "60:89:B1": "Key Digital Systems",
    "60:8B:0E": "Apple",
    "60:8C:4A": "Apple",
    "60:92:17": "Apple",
    "60:95:32": "Apple",
    "60:A3:7D": "Apple",
    "60:C5:47": "Apple",
    "60:D0:A9": "Samsung",
    "60:F8:1D": "Apple",
    "64:16:66": "Nest Labs",
    "64:20:0C": "Apple",
    "64:27:37": "Hon Hai / Foxconn",
    "64:5A:04": "Chicony Electronics",
    "64:70:02": "TP-Link",
    "64:76:BA": "Apple",
    "64:89:9A": "LG Electronics",
    "64:B9:E8": "Apple",
    "64:BC:0C": "LG Electronics",
    "64:CC:2E": "Xiaomi",
    "64:D8:14": "Cisco-Linksys",
    "64:E6:82": "Apple",
    "68:05:CA": "Intel",
    "68:09:27": "Apple",
    "68:17:29": "Intel",
    "68:5B:35": "Apple",
    "68:96:7B": "Apple",
    "68:9C:70": "Apple",
    "68:A8:6D": "Apple",
    "68:AE:20": "Apple",
    "68:BC:0C": "Cisco Meraki",
    "68:FE:F7": "Apple",
    "6C:19:8F": "D-Link",
    "6C:20:56": "Cisco",
    "6C:2F:2C": "Samsung",
    "6C:3E:6D": "Apple",
    "6C:40:08": "Apple",
    "6C:62:6D": "Micro-Star International",
    "6C:72:20": "Apple",
    "6C:8D:C1": "Cisco",
    "6C:94:66": "Intel",
    "6C:F0:49": "GIGA-BYTE",
    "70:3E:AC": "Apple",
    "70:48:0F": "Apple",
    "70:56:81": "Apple",
    "70:70:0D": "Apple",
    "70:73:CB": "Apple",
    "70:85:C2": "ASRock",
    "70:E4:22": "Cisco",
    "70:E7:2C": "Apple",
    "70:EA:1A": "Cisco",
    "70:EA:5A": "Apple",
    "70:EC:E4": "Apple",
    "70:EF:00": "Apple",
    "70:F0:87": "Apple",
    "74:2F:68": "AzureWave",
    "74:81:14": "Apple",
    "74:83:C2": "Ubiquiti",
    "74:86:0B": "Cisco",
    "74:86:7A": "Dell",
    "74:86:E2": "Dell",
    "74:C2:46": "Amazon Technologies",
    "74:D0:2B": "ASUSTek",
    "74:E1:B6": "Apple",
    "78:24:AF": "ASUSTek",
    "78:31:C1": "Apple",
    "78:4F:43": "Apple",
    "78:67:D7": "Samsung",
    "78:7B:8A": "Apple",
    "78:9F:70": "Apple",
    "78:A3:E4": "Apple",
    "78:CA:39": "Apple",
    "78:DD:08": "Hon Hai / Foxconn",
    "78:E3:B5": "Hewlett Packard",
    "7C:01:91": "Apple",
    "7C:04:D0": "Apple",
    "7C:11:BE": "Apple",
    "7C:1C:F1": "Apple",
    "7C:2E:BD": "Google",
    "7C:50:49": "Apple",
    "7C:61:66": "Amazon Technologies",
    "7C:6D:62": "Apple",
    "7C:C3:A1": "Apple",
    "7C:D1:C3": "Apple",
    "7C:F0:5F": "Apple",
    "80:00:6E": "Apple",
    "80:19:34": "Intel",
    "80:38:96": "Sharp",
    "80:49:71": "Apple",
    "80:58:F8": "Motorola Mobility",
    "80:65:7C": "Apple",
    "80:86:F2": "Intel",
    "80:92:9F": "Apple",
    "80:AD:16": "Xiaomi",
    "80:B0:3D": "Apple",
    "80:BE:05": "Apple",
    "80:C7:55": "Panasonic",
    "80:E6:50": "Apple",
    "84:29:99": "Apple",
    "84:38:35": "Apple",
    "84:47:09": "Hewlett Packard",
    "84:85:06": "Apple",
    "84:8E:0C": "Apple",
    "84:A1:34": "Apple",
    "84:AD:8D": "Apple",
    "84:B1:53": "Apple",
    "84:B1:E4": "Apple",
    "84:FC:AC": "Apple",
    "88:1F:A1": "Apple",
    "88:30:8A": "Murata Manufacturing",
    "88:53:95": "Apple",
    "88:63:DF": "Apple",
    "88:66:A5": "Apple",
    "88:6B:0F": "Apple",
    "88:C9:D0": "LG Electronics",
    "88:CB:87": "Apple",
    "88:E9:FE": "Apple",
    "8C:04:FF": "Dell",
    "8C:29:37": "Apple",
    "8C:2D:AA": "Apple",
    "8C:58:77": "Apple",
    "8C:7B:9D": "Apple",
    "8C:85:90": "Apple",
    "8C:89:A5": "Micro-Star International",
    "8C:AE:4C": "Plugable Technologies",
    "8C:FA:BA": "Apple",
    "90:09:D0": "Synology",
    "90:18:7C": "Samsung",
    "90:27:E4": "Apple",
    "90:3C:92": "Apple",
    "90:56:82": "Lenovo Mobile",
    "90:72:40": "Apple",
    "90:84:0D": "Apple",
    "90:B2:1F": "Apple",
    "90:B9:31": "Apple",
    "90:DD:5D": "Cisco",
    "90:E2:BA": "Intel",
    "90:F6:52": "TP-Link",
    "94:10:3E": "Belkin",
    "94:35:0A": "Samsung",
    "94:94:26": "Apple",
    "94:B0:0D": "Intel",
    "94:B1:0A": "Samsung",
    "94:E9:79": "Lite-On",
    "98:01:A7": "Apple",
    "98:03:D8": "Apple",
    "98:5A:EB": "Apple",
    "98:B8:E3": "Apple",
    "98:CA:33": "Apple",
    "98:D6:BB": "Apple",
    "98:E0:D9": "Apple",
    "9C:04:EB": "Apple",
    "9C:20:7B": "Apple",
    "9C:2A:70": "Hon Hai / Foxconn",
    "9C:35:EB": "Apple",
    "9C:4E:36": "Apple",
    "9C:84:BF": "Apple",
    "9C:8E:99": "Hewlett Packard",
    "9C:9D:7E": "Ubiquiti",
    "9C:B7:0D": "Lite-On",
    "9C:FC:01": "Apple",
    "A0:02:DC": "Amazon Technologies",
    "A0:18:28": "Apple",
    "A0:1D:48": "Hewlett Packard",
    "A0:78:17": "Apple",
    "A0:88:B4": "Intel",
    "A0:99:9B": "Apple",
    "A0:C5:89": "Intel",
    "A0:D3:C1": "Hewlett Packard",
    "A0:D7:95": "Apple",
    "A0:E4:53": "Sony",
    "A4:5E:60": "Apple",
    "A4:67:06": "Apple",
    "A4:77:33": "Google",
    "A4:83:E7": "Apple",
    "A4:B1:C1": "Apple",
    "A4:BA:DB": "Dell",
    "A4:BB:6D": "Dell",
    "A4:CF:12": "Apple",
    "A4:D1:8C": "Apple",
    "A4:D1:D2": "Apple",
    "A4:D2:3E": "Apple",
    "A8:20:66": "Apple",
    "A8:5B:78": "Apple",
    "A8:66:7F": "Apple",
    "A8:86:DD": "Apple",
    "A8:88:08": "Apple",
    "A8:8E:24": "Apple",
    "A8:8F:D9": "Apple",
    "A8:91:3D": "Apple",
    "A8:96:75": "Motorola Mobility",
    "A8:BB:CF": "Apple",
    "A8:FA:D8": "Apple",
    "AC:16:2D": "Hewlett Packard",
    "AC:37:43": "Hewlett Packard",
    "AC:3C:0B": "Apple",
    "AC:61:75": "Huawei",
    "AC:7F:3E": "Apple",
    "AC:87:A3": "Apple",
    "AC:BC:32": "Apple",
    "AC:CF:5C": "Apple",
    "B0:34:95": "Apple",
    "B0:48:7A": "TP-Link",
    "B0:52:16": "Apple",
    "B0:65:BD": "Apple",
    "B0:70:2D": "Apple",
    "B0:72:BF": "Murata Manufacturing",
    "B0:9F:BA": "Apple",
    "B0:C4:E7": "Samsung",
    "B0:CA:68": "Apple",
    "B0:DF:3A": "Samsung",
    "B4:18:D1": "Apple",
    "B4:31:61": "Apple",
    "B4:52:7D": "Sony",
    "B4:62:93": "Apple",
    "B4:74:9F": "ASKEY Computer",
    "B4:8B:19": "Apple",
    "B4:F0:AB": "Apple",
    "B8:09:8A": "Apple",
    "B8:17:C2": "Apple",
    "B8:27:EB": "Raspberry Pi",
    "B8:2A:72": "Dell",
    "B8:2A:A9": "Apple",
    "B8:63:4D": "Apple",
    "B8:78:2E": "Apple",
    "B8:8D:12": "Apple",
    "B8:BE:BF": "Cisco",
    "B8:BF:83": "Intel",
    "B8:C1:11": "Apple",
    "B8:C7:5D": "Apple",
    "B8:CA:3A": "Dell",
    "B8:CB:29": "Dell",
    "B8:E8:56": "Apple",
    "B8:F6:B1": "Apple",
    "BC:20:A4": "Samsung",
    "BC:3B:AF": "Apple",
    "BC:52:B7": "Apple",
    "BC:67:78": "Apple",
    "BC:76:70": "Hewlett Packard",
    "BC:92:6B": "Apple",
    "BC:AE:C5": "ASUSTek",
    "BC:C1:68": "DinBox Sweden",
    "BC:E1:43": "Apple",
    "BC:EE:7B": "ASUSTek",
    "C0:18:85": "Hon Hai / Foxconn",
    "C0:25:A5": "Dell",
    "C0:56:27": "Tenda",
    "C0:63:94": "Apple",
    "C0:84:7A": "Apple",
    "C0:9F:42": "Apple",
    "C0:A5:3E": "Apple",
    "C0:CC:F8": "Apple",
    "C0:CE:CD": "Apple",
    "C0:F2:FB": "Apple",
    "C4:2C:03": "Apple",
    "C4:34:6B": "Hewlett Packard",
    "C4:46:19": "Hon Hai / Foxconn",
    "C4:8E:8F": "Hon Hai / Foxconn",
    "C4:9D:ED": "Microsoft",
    "C4:AB:8C": "Apple",
    "C4:B3:01": "Apple",
    "C4:B9:CD": "Cisco",
    "C4:CB:6B": "Airista Flow",
    "C4:CB:E1": "Dell",
    "C8:2A:14": "Apple",
    "C8:3A:35": "Tenda",
    "C8:3C:85": "Apple",
    "C8:69:CD": "Apple",
    "C8:6F:1D": "Apple",
    "C8:9C:DC": "Elitegroup Computer Systems",
    "C8:BC:C8": "Apple",
    "C8:D0:83": "Apple",
    "C8:E0:EB": "Apple",
    "C8:F6:50": "Apple",
    "CC:08:8D": "Apple",
    "CC:20:E8": "Apple",
    "CC:25:EF": "Apple",
    "CC:29:F5": "Apple",
    "CC:3E:5F": "Hewlett Packard",
    "CC:44:63": "Apple",
    "CC:46:D6": "Cisco",
    "CC:78:5F": "Apple",
    "CC:95:D7": "Vizio",
    "CC:9F:35": "Apple",
    "CC:C7:60": "Apple",
    "CC:D2:81": "Apple",
    "D0:03:4B": "Apple",
    "D0:23:DB": "Apple",
    "D0:25:98": "Apple",
    "D0:37:45": "TP-Link",
    "D0:39:72": "Texas Instruments",
    "D0:50:99": "ASRock",
    "D0:57:7B": "Intel",
    "D0:81:7A": "Apple",
    "D0:A6:37": "Apple",
    "D0:C5:F3": "Apple",
    "D0:E1:40": "Apple",
    "D0:E7:82": "AzureWave",
    "D4:38:9C": "Sony",
    "D4:61:9D": "Apple",
    "D4:9A:20": "Apple",
    "D4:9A:A0": "Hon Hai / Foxconn",
    "D4:DC:CD": "Apple",
    "D4:F4:6F": "Apple",
    "D8:00:4D": "Apple",
    "D8:1D:72": "Apple",
    "D8:30:62": "Apple",
    "D8:3A:DD": "Raspberry Pi",
    "D8:3B:BF": "Intel",
    "D8:80:83": "Apple",
    "D8:96:95": "Apple",
    "D8:A2:5E": "Apple",
    "D8:BB:2C": "Apple",
    "D8:CF:9C": "Apple",
    "D8:D1:CB": "Apple",
    "D8:FC:93": "Intel",
    "DC:2B:2A": "Apple",
    "DC:37:14": "Apple",
    "DC:53:60": "Intel",
    "DC:56:E7": "Apple",
    "DC:A5:F4": "Cisco",
    "DC:A6:32": "Raspberry Pi",
    "DC:A9:04": "Apple",
    "DC:BB:C9": "Apple",
    "DC:E8:38": "Apple",
    "E0:06:E6": "Hon Hai / Foxconn",
    "E0:CB:1D": "Private",
    "E0:CB:4E": "Intel",
    "E0:DB:55": "Dell",
    "E0:F5:C6": "Apple",
    "E0:F8:47": "Apple",
    "E4:25:E7": "Apple",
    "E4:40:E2": "Samsung",
    "E4:42:A6": "Intel",
    "E4:43:4B": "Dell",
    "E4:5D:37": "Juniper",
    "E4:5E:1B": "Google",
    "E4:5E:37": "Intel",
    "E4:5F:01": "Raspberry Pi",
    "E4:60:17": "Intel",
    "E4:62:C4": "Cisco",
    "E4:7C:F9": "Samsung",
    "E4:8B:7F": "Apple",
    "E4:98:D1": "Microsoft",
    "E4:CE:8F": "Apple",
    "E8:04:0B": "Apple",
    "E8:06:88": "Apple",
    "E8:39:35": "Hewlett Packard",
    "E8:40:40": "Cisco",
    "E8:80:2E": "Apple",
    "E8:8D:28": "Apple",
    "E8:B2:AC": "Apple",
    "E8:BB:A8": "Apple",
    "E8:CC:18": "D-Link",
    "E8:DE:27": "TP-Link",
    "EC:35:86": "Apple",
    "EC:85:2F": "Apple",
    "EC:FA:BC": "Huawei",
    "F0:18:98": "Apple",
    "F0:24:75": "Apple",
    "F0:25:B7": "Samsung",
    "F0:27:65": "Murata Manufacturing",
    "F0:72:8C": "Samsung",
    "F0:76:1C": "Samsung",
    "F0:99:BF": "Apple",
    "F0:B4:79": "Apple",
    "F0:C3:71": "Apple",
    "F0:C7:25": "Apple",
    "F0:CD:31": "Samsung",
    "F0:D1:A9": "Apple",
    "F0:D2:F1": "Amazon Technologies",
    "F0:D3:1F": "Apple",
    "F0:D4:15": "Intel",
    "F0:D4:E2": "Dell",
    "F0:DB:E2": "Apple",
    "F0:DB:F8": "Apple",
    "F0:DC:E2": "Apple",
    "F4:0F:24": "Apple",
    "F4:1B:A1": "Apple",
    "F4:31:C3": "Apple",
    "F4:5C:89": "Apple",
    "F4:F1:5A": "Apple",
    "F4:F5:D8": "Google",
    "F4:EC:38": "TP-Link",
    "F8:0F:F9": "Google",
    "F8:16:54": "Intel",
    "F8:1E:DF": "Apple",
    "F8:27:93": "Apple",
    "F8:2F:A8": "Hon Hai / Foxconn",
    "F8:59:71": "Intel",
    "F8:8F:CA": "Google",
    "F8:95:C7": "Apple",
    "F8:B1:56": "Dell",
    "F8:B1:DD": "Apple",
    "F8:C3:CC": "Apple",
    "F8:C6:50": "Cisco",
    "F8:CA:B8": "Dell",
    "F8:DB:88": "Dell",
    "FC:25:3F": "Apple",
    "FC:64:BA": "Apple",
    "FC:C2:DE": "Samsung",
    "FC:D8:48": "Apple",
    "FC:FB:FB": "Cisco",
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
