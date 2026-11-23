# Test fixtures

`test-rsa-private.pem` and `test-rsa-public.pem` are a throwaway RSA key pair
generated only for these tests. The private key is public by design (it is in
this repository): it protects nothing, signs nothing outside the fake issuer and
sidecar the tests start on loopback, and must never be reused, deployed or
copied into a real key file.

Real Zitadel machine-user keys are provisioned out of band, live in a secret
store and reach the server only through `--backlinks-key-file`.

`test-rsa-private-pkcs8.pem` is the same private key re-encoded as PKCS#8
(`openssl pkcs8 -topk8 -nocrypt`), used to check that both PEM encodings are
accepted.
