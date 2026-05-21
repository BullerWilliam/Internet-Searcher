# Advanced IP Scanner

A powerful Python GUI application that scans your network to find all connected devices and their shared resources (printers, file shares).

## Features

- **Advanced IP Range Input**: Specify ranges like `192.168.0.1-254` or use CIDR notation `192.168.0.0/24`
- **Fast Parallel Scanning**: Scans 50 IPs in parallel for blazing-fast results
- **Device Discovery**: Finds IP addresses, computer names, and MAC addresses
- **Manufacturer Identification**: Displays device manufacturer based on MAC address
- **Resource Discovery**: Automatically finds shared printers and file shares on discovered devices
- **Hierarchical Tree View**: Shows devices with nested resources (printers, shares)
- **Live Status Updates**: Real-time feedback on scan progress
- **Professional UI**: Menu bar, toolbar, tabs, and detailed status information
- **Multi-threaded**: Non-blocking UI during scans

## Requirements

- Python 3.7+
- Windows (uses Windows-specific network tools like `ping`, `arp`, and `net`)
- Administrator privileges recommended for best results

## Installation

1. Install dependencies:
```bash
pip install -r requirements.txt
```

2. Run the application:
```bash
python network_info_app.py
```

## Usage

1. **Enter IP Range**: In the toolbar, specify an IP range:
   - Single IP: `192.168.0.100`
   - Range: `192.168.0.1-254`
   - CIDR: `192.168.0.0/24`

2. **Click "Scan"**: Start the network scan

3. **View Results**: Discovered devices appear in the tree view showing:
   - Status indicator (●)
   - Computer name
   - IP address
   - Manufacturer
   - MAC address
   - Nested resources (Printers, Shares)

4. **Status Bar**: Shows count of alive/dead/unknown devices

## How It Works

- **Ping Sweep**: Sends ICMP ping packets to all addresses in the specified range
- **Hostname Resolution**: Uses reverse DNS and NetBIOS (nbtstat) for computer names
- **MAC Lookup**: Queries ARP table and identifies manufacturer from MAC prefix
- **Resource Enumeration**: Uses Windows `net view` command to find shared printers and file shares

## Output

The tree structure displays:
```
● Computer_Name (192.168.0.100) - Hewlett Packard
  Printer
    → HP LaserJet M1522 series
  Share
    → Documents
    → Downloads
```

## Performance

- Scans 256 IPs (typical /24 subnet) in **5-15 seconds** depending on network responsiveness
- Uses 50 parallel threads for optimal performance
- Dead/unreachable IPs detected quickly (500ms ping timeout)

## Notes

- Some devices may not resolve hostnames if DNS/NetBIOS is unavailable
- Network resources may require specific permissions to enumerate
- Running with Administrator privileges provides better resource discovery
- Firewall rules may prevent resource enumeration on some devices
