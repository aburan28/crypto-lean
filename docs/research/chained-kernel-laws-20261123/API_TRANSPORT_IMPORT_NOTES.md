# Exact Git-data transport

API commit f6c3685 matches the complete locally prepared tree. The first
raw-commit reconstruction assumed +0000 timezones and failed its SHA check
before any ref change. Enumerating timezone text encodings against the known
remote SHA reconstructed the exact commit; the branch was then fast-forwarded
locally. A following remote-tracking update expected a previously absent ref
and failed; creating that owned metadata ref with an all-zero expected lease
completed the import. No source/index content or external branch was forced.
[pcc:unverified]

The metadata-helper writer completed the helper, then an unused timestamp assignment failed with NameError before any staging/publication/proof call. The next operation supplies the import explicitly. The exact remote commit used -0800 timezone text; the earlier +0000 reconstruction assumption was false. [pcc:unverified]
