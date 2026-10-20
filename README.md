# PyVM Web — experimental adapter

This wraps your existing Pygame desktop in a web-accessible MJPEG stream. It is a **single shared desktop**, not a multi-user VM. All visitors with the token see/control the same session and share its files. Use only with trusted testers; do not expose publicly without stronger authentication, rate limiting and isolation.

## Local setup

1. Install Python 3.11+ and open this folder in VS Code.
2. Create a virtual environment: `python -m venv .venv`
3. Activate it (Windows PowerShell: `.venv\\Scripts\\Activate.ps1`; macOS/Linux: `source .venv/bin/activate`).
4. Run `pip install -r requirements.txt`.
5. Set a long random token: PowerShell `$env:PYVM_TOKEN="replace-with-a-long-random-secret"`; macOS/Linux `export PYVM_TOKEN="replace-with-a-long-random-secret"`.
6. Run `python server.py`.
7. Open `http://127.0.0.1:5000/?token=YOUR_TOKEN` in your own browser.

## Deployment

Use a Linux host/container that supports Python and SDL dummy video. Set `PYVM_TOKEN` as a private environment variable and `PORT` to the platform-assigned port (the program reads it automatically). Start command: `python server.py`. Use HTTPS in production. Hosts that suspend processes or have ephemeral storage may reset your VM or delete `vm_disk.json` between restarts. The embedded Flask server is a development server; use a production deployment architecture before public use.

## Known limitations

- Single shared session and disk. Not suitable for several friends at once.
- Keyboard layout, shortcuts, mouse dragging and browser sub-app may be imperfect.
- Pygame desktop's built-in Playwright browser may not run on all hosting platforms.
- File import/export uses Tkinter dialogs, which do not work in a headless browser/server; these need web upload/download endpoints in a later iteration.
- 12 FPS JPEG stream is bandwidth-heavy and less responsive than WebRTC/WebSocket streaming.
- Does not bypass managed Chromebook/network policies.
