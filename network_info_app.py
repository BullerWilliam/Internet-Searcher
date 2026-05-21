import json
import socket
import threading
import tkinter as tk
from tkinter import ttk
from urllib.error import URLError
from urllib.request import urlopen


PUBLIC_IP_URL = "https://api.ipify.org?format=json"


def get_local_hostname() -> str:
    return socket.gethostname()


def get_local_ipv4_addresses() -> list[str]:
    addresses = set()
    hostname = socket.gethostname()

    try:
        for result in socket.getaddrinfo(hostname, None, family=socket.AF_INET):
            ip_address = result[4][0]
            if not ip_address.startswith("127."):
                addresses.add(ip_address)
    except socket.gaierror:
        pass

    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
            sock.connect(("8.8.8.8", 80))
            addresses.add(sock.getsockname()[0])
    except OSError:
        pass

    return sorted(addresses)


def get_public_ip() -> str:
    try:
        with urlopen(PUBLIC_IP_URL, timeout=5) as response:
            payload = json.loads(response.read().decode("utf-8"))
            return payload.get("ip", "Unavailable")
    except (URLError, TimeoutError, OSError, json.JSONDecodeError):
        return "Unavailable"


class NetworkInfoApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Network Info Viewer")
        self.root.geometry("720x420")
        self.root.minsize(620, 360)

        self.hostname_var = tk.StringVar(value="Loading...")
        self.public_ip_var = tk.StringVar(value="Loading...")
        self.status_var = tk.StringVar(value="Ready")

        self._build_layout()
        self.refresh()

    def _build_layout(self) -> None:
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)

        outer = ttk.Frame(self.root, padding=16)
        outer.grid(row=0, column=0, sticky="nsew")
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(1, weight=1)

        header = ttk.Frame(outer)
        header.grid(row=0, column=0, sticky="ew", pady=(0, 12))
        header.columnconfigure(0, weight=1)

        ttk.Label(
            header,
            text="Current Network Information",
            font=("Segoe UI", 16, "bold"),
        ).grid(row=0, column=0, sticky="w")

        ttk.Button(header, text="Refresh", command=self.refresh).grid(
            row=0, column=1, sticky="e"
        )

        content = ttk.Frame(outer)
        content.grid(row=1, column=0, sticky="nsew")
        content.columnconfigure(0, weight=1)
        content.columnconfigure(1, weight=1)
        content.rowconfigure(1, weight=1)

        summary = ttk.LabelFrame(content, text="Summary", padding=12)
        summary.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 12))
        summary.columnconfigure(1, weight=1)

        ttk.Label(summary, text="Computer name:").grid(row=0, column=0, sticky="w")
        ttk.Label(summary, textvariable=self.hostname_var).grid(
            row=0, column=1, sticky="w", padx=(12, 0)
        )

        ttk.Label(summary, text="Public IP:").grid(row=1, column=0, sticky="w", pady=(8, 0))
        ttk.Label(summary, textvariable=self.public_ip_var).grid(
            row=1, column=1, sticky="w", padx=(12, 0), pady=(8, 0)
        )

        local_frame = ttk.LabelFrame(content, text="Local IPv4 Addresses", padding=12)
        local_frame.grid(row=1, column=0, sticky="nsew", padx=(0, 6))
        local_frame.columnconfigure(0, weight=1)
        local_frame.rowconfigure(0, weight=1)

        self.local_ip_list = tk.Listbox(local_frame, height=10)
        self.local_ip_list.grid(row=0, column=0, sticky="nsew")

        notes_frame = ttk.LabelFrame(content, text="Notes", padding=12)
        notes_frame.grid(row=1, column=1, sticky="nsew", padx=(6, 0))
        notes_frame.columnconfigure(0, weight=1)
        notes_frame.rowconfigure(0, weight=1)

        notes = (
            "This app shows information for the current computer and its active "
            "internet connection.\n\n"
            "It does not scan the network for other devices, IP ranges, or hostnames."
        )
        ttk.Label(notes_frame, text=notes, wraplength=260, justify="left").grid(
            row=0, column=0, sticky="nw"
        )

        status_bar = ttk.Label(outer, textvariable=self.status_var, anchor="w")
        status_bar.grid(row=2, column=0, sticky="ew", pady=(12, 0))

    def refresh(self) -> None:
        self.status_var.set("Refreshing network details...")
        self.hostname_var.set("Loading...")
        self.public_ip_var.set("Loading...")
        self.local_ip_list.delete(0, tk.END)
        self.local_ip_list.insert(tk.END, "Loading...")

        worker = threading.Thread(target=self._load_data, daemon=True)
        worker.start()

    def _load_data(self) -> None:
        hostname = get_local_hostname()
        local_ips = get_local_ipv4_addresses()
        public_ip = get_public_ip()
        self.root.after(0, self._apply_data, hostname, local_ips, public_ip)

    def _apply_data(self, hostname: str, local_ips: list[str], public_ip: str) -> None:
        self.hostname_var.set(hostname)
        self.public_ip_var.set(public_ip)
        self.local_ip_list.delete(0, tk.END)

        if local_ips:
            for ip_address in local_ips:
                self.local_ip_list.insert(tk.END, ip_address)
        else:
            self.local_ip_list.insert(tk.END, "No active IPv4 addresses found")

        self.status_var.set("Refresh complete")


def main() -> None:
    root = tk.Tk()
    style = ttk.Style()
    if "vista" in style.theme_names():
        style.theme_use("vista")
    app = NetworkInfoApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
