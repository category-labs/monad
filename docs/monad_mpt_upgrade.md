# monad-mpt --upgrade

## When to run

Run `monad-mpt --upgrade` once on each monad node after upgrading the
monad apt package to a release that advances the on-disk metadata
version. Today that means: any upgrade that crosses from a pre-MONAD008
package to a MONAD008-or-later package.

If the package notes do not mention a metadata version bump, `--upgrade`
is still safe to run (it is a no-op on an already-current pool, ending
in a metadata flush), but it is not required.

## Runbook

1. Stop all monad services that access the DB (monad-node, any
   supporting services). Confirm with `systemctl status` or
   equivalent.
2. `apt install monad=<new-version>` (or the equivalent for your
   package manager).
3. Run the upgrade, pointing at the same storage sources your services
   use:
   ```
   monad-mpt --upgrade --storage /dev/<device1> [--storage /dev/<device2> ...]
   ```
   The command exits 0 on success. Typical runtime is sub-second: the
   tool only touches the cnv metadata chunk, not seq data.
4. Start services.

## Reading the output

- `Migrated DB metadata from MONAD007 to MONAD008.` — an on-disk
  migration happened.
- `DB is on version MONAD008; flushing metadata...` — the tool
  confirms the final state and flushes the metadata to disk for
  durability. Printed both when the DB was already MONAD008 and when
  the ctor just migrated it from MONAD007 (the `Migrated DB metadata`
  line above distinguishes the two).
- `WARNING: --upgrade found no existing DB metadata; a fresh MONAD008
  pool was created.` — the storage device had no prior DB. You probably
  meant to run `--create` on a fresh device; the resulting pool is
  well-formed but empty.
- `Success.` — exit 0 on the final line.

## If a service fails to start with "DB is on older format"

A service binary observed `PREVIOUS_MAGIC` on the DB and refused to
auto-migrate. This is by design: services never run migrations. Stop
all services, run `monad-mpt --upgrade`, then start services again.

## Safety

`monad-mpt --upgrade` is safe to re-run. It is idempotent on
already-current pools, and the migration itself is crash-safe (each
metadata copy is migrated under a dirty guard; a crash mid-migration
heals on the next writable open that has `allow_migration = true`).

Running `monad-mpt --upgrade` while a monad service is accessing the DB
is not supported. Follow the runbook and stop services first.
