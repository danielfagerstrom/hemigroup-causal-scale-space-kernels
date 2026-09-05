# Library acquisition inbox

Needs recorded by a **cloud** session, waiting for a desktop to replay them into the real
Zotero "To Acquire" queue.

The cloud librarian runs in reader mode with a read-only Drive credential, so
`library acquire request` cannot write the Zotero stub itself. It writes one JSON file per
need here instead, and git carries it to the desktop — the librarian's designed cloud path,
with no new credential.

## Draining it

The normal inbox lives in the wiki vault, which is not checked out in cloud sessions, so
these were filed into this repo and the desktop needs to be pointed at them:

    library acquire drain --inbox notes/library-inbox --dry-run
    library acquire drain --inbox notes/library-inbox

`drain` removes each file as it replays it, so the directory empties itself and the entries
show up in `library acquire list` exactly as desk-filed ones do.

## What is in a file

`schema`, the free-text `text` that becomes the stub, `requested_for` (the citekey of the
source that cites it), the acquisition `note`, and `requested_at`.

The note is where a request earns its keep: it records **why** the source is wanted and
**what a search already ruled out**, so the acquisition does not have to rediscover either.
It also flags which metadata is verified and which is not — a cloud session often cannot
reach the publisher, and unverified volume or page numbers must never be filed as if they
were checked.
