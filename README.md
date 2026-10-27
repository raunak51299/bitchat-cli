# bitchat CLI — chat with the OFFICIAL bitchat app over the internet

This is a Windows-friendly command-line client for the **official bitchat app's
internet mode**. A phone running the real bitchat app and this CLI can meet in
the same location ("geohash") channels and chat with each other.

No Bluetooth mesh is used here (PCs have none) — this is the app's Nostr-based
internet side, implemented against its published protocol
([bitchat-android](https://github.com/permissionlesstech/bitchat-android) /
[bitchat](https://github.com/permissionlesstech/bitchat) whitepaper).

## Quick start

```
run.bat                     (bootstraps the venv on first run and launches)
```

Then:

```
/geo 43.6532,-79.3832          join the city/block channel of your coordinates
/geo 40.7128,-74.0060 city     join New York City channel (level = city)
/geo dr                        join Northeast-US region channel directly
/who                           who is here
hello everyone ...             plain text = chat message
/q                             quit
```

`--nick <name>` sets your nickname (also `/nick name` at run time).
`--geo "lat,lon"` or `--geo dr5rsj7` joins right at startup.
`--tui` switches to the alternate-screen UI (message pane, status bar, fixed
input line — `PageUp`/`PageDown` or `↑`/`↓` scroll back (`Home` jumps to the
oldest page, `End` returns to live), `Ctrl+L` clears).

## How the internet mode works (exactly like the phone app)

Phones pick a location channel: region -> province -> city -> neighborhood ->
block (geohashes of 2/4/5/6/7/8 chars). On the wire:

* **chat** — ephemeral Nostr event **kind 20000**
  `tags: g=<geohash>, n=<nickname>` and the message is the plaintext content
* **presence** — **kind 20001** heartbeats every 40–80 s, empty content
* events are standard **NIP-01** events (event id = sha256 over compact JSON
  `[0, pubkey, created_at, kind, tags, content]`) signed with **BIP-340 schnorr**
* **identity** — one Nostr keypair *per geohash*, derived deterministically from
  a device seed: `HMAC-SHA256(seed, geohash || counter)` + valid-key fallback,
  the very same scheme as the app. Every channel is a different pseudonym and
  getting a `npub` in one channel almost never leads back to other channels.
* **relays** — the 5 relays closest to the geohash center, from the same
  auto-updated relay directory the app ships
  ([georelays CSV](https://github.com/permissionlesstech/georelays))
* participants expire after 5 minutes of silence (app behavior)

This client validates every event the same way the app does: NIP-01 event id
recompute, schnorr signature (pure-Python secp256k1 in `secp.py`, tested against
the official BIP-340 test vectors), client-side `#g` tag filter and dedup.

To keep live chat live, the expensive pure-Python signature check runs in
background workers (the event id is re-checked cheaply inline first), and the
feed is applied strictly in arrival order — a backlog burst never stalls
real-time delivery. Duplicates that arrive via your 5 relays are dropped
before any signature work. When a relay drops and reconnects, it re-requests
only its own gap (up to ~2 minutes), not another full hour of backlog.

Verified against the live network: event ids of third-party Nostr events
recompute byte-exact (8/8) and third-party signatures verify (8/8); selftest
exchanges messages between two CLI peers (two "phones") through real relays.

## Important expectations

* **Ephemeral by design.** Relays do not store kind 20000/20001 events; a
  message only reaches people who are in the channel *at the same time*. If
  `#geohash` is silent, nobody is around — try a wider channel (city or region
  level, e.g. `/geo dr` for the US northeast or `--sniff` to scout).
* **Private messages: envelope-only on the PC.** DMs arrive as kind 1059
  gift wraps addressed to your per-channel key. The CLI opens the envelope
  (unwraps the NIP-44 layers, verifies the seal, shows who/when sent) and
  prints a `[dm]` line — but the DM *body* is a mesh-Noise session packet
  whose session exists only on phones (born over Bluetooth handshakes), so
  the text stays readable on your phone. Phone users will still show up
  in `[dm]` lines even if they DM you while you're only in the CLI.
* **Public chat is plaintext and visible to relays** — same as the app's
  location channels; DMs are the encrypted part, and they need the phone.
* Nickname is taken from your own settings (max 15 chars, like the app).
  Phone users you haven't spoken yet display as their `n` tag or `anon`.

## Commands

```
/geo <lat,lon> [level]         level: region(2) province(4) city(5)
                                      neighborhood(6) block(7) building(8)
/geo <geohash>                 direct (2–8 base32 chars)
/geo                           show current channel
/who                           participants (last 5 min)
/relays                        nearest relay status
/npub                          your per-channel npub (changes per channel)
/nick <name>                   set nickname
/msg                           DM handling explained (envelope-only here)
/alert on|off                  bell + bold when someone mentions you (saved)
/history [N]                   last N messages of this session (default 20)
/last <nick>                   recent messages from one person
/find <text>                   search the session in this channel
/set                           relay override / boost / proxy (settings.json)
/set relays <url1,url2|off>    pin your own relays instead of nearest-5
/set boost <url1,url2|off>     publish through extra relays too
/set proxy <url|off>           http:// or socks5:// (e.g. Tor 127.0.0.1:9050)
/clear · /help · /q            housekeeping
```

## Chat features

* **Grouped messages** — consecutive messages from one person share a single
  `HH:MM nick` header; every user keeps their own color.
* **Sent/relayed dot** — your own messages show `●` yellow while sending and
  turn `●` green in place as soon as a relay confirms them.
* **Mention alerts** — a line containing your nick rings the terminal bell
  and bolds your name; `/alert off` silences it (persisted).
* **Liveliness lines** — `sam joined` / `sam left` / nickname changes appear
  as dim system lines after a ~35 s settle (so the backlog join burst stays
  quiet).
* **Session log** — every channel is also archived to
  `~/.bitchat-cli/logs/<geohash>.log` (UTC stamps, own messages as `you`);
  `/history`, `/last`, `/find` search the in-memory session.
* **NIP-13 proof-of-work** — if a relay rejects an event demanding PoW, the
  same message is re-mined in a background thread and retried to that relay
  (supported natively in the app's NostrProofOfWork module).
* **Relay health** — relays with broken TLS certificates are skipped for an
  hour after a failure, and same-host variants (`host` / `host:443`) count
  once; user picks via `--relays` / `--boost-relays` always win.

## Files

| file | purpose |
|---|---|
| `bitchat.py` | the CLI client (official internet-mode protocol, DM envelope, TUI) |
| `secp.py` | secp256k1 + BIP-340 (secret-key math via OpenSSL) (validated on all 19 official vectors) |
| `nostr_relays.csv` | bundled copy of the app's relay directory (auto-refreshed to `~/.bitchat-cli/`) |
| `run.bat` | double-click launcher (venv + deps) |

State lives in `~/.bitchat-cli/`:

* `nostr.json` — device seed, nickname, last channel. **Keep it private**: it
  owns every geohash pseudonym.
* `settings.json` — persisted prefs: pinned/boosted relays, proxy, alert
  toggle, one-hour TLS-failure blacklist.
* `logs/<geohash>.log` — archived channel traffic (plain text, UTC stamps);
  DM bodies are never written here.

## Diagnostics

```
python bitchat.py --selftest           offline + live tests (needs internet)
python bitchat.py --sniff u4pru --seconds 60   watch a channel passively
```

`--sniff <geohash>` shows raw kind 20000/20001 traffic; use it to scout a
channel before joining. Example busy channels are the region channels of large
areas (e.g. `dr` for the US northeast), where phone users hang out.

## Troubleshooting

* **Messages arrive late** — after a flaky-relay disconnect the CLI replays
  only ~2 minutes of that relay's gap; if relays sit at `retry in Ns` under
  `/relays` for a while, those moments stay missing (ephemeral design). A
  message timestamped long before its arrival is simply one that was sent
  while that relay was unreachable.
* **"not delivered / nobody sees me"** — wait a minute: presence cycles are
  40–80 s. `/relays` shows connectivity; flaky cell-tower relays retry forever.
* **Relay selection looks odd** — the relay directory is community-driven and
  its entries age: hosts with expired certificates are auto-skipped for an
  hour, and `--relays relay.a,relay.b` pins a set you trust (or `/set relays`).
* **Behind Tor / a proxy** — `--proxy socks5://127.0.0.1:9050` (or `/set
  proxy`) routes all relay WebSocket traffic through it.
* **Clock skew** — very wrong PC time can make your events land outside the
  1-hour backlog window; keep Windows time synced.
* **Firewall blocks wss** — this needs plain outbound TCP 443 (like any HTTPS).
* **Word of caution** — public geochannel nicknames are not authenticated
  identities beyond the keypair; the app itself shows the same faces.
