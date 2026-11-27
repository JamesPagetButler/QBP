import subprocess, sys, pathlib

out = pathlib.Path(sys.argv[1])
for v in [
    "v4_31_0",
    "v4_32_0",
    "v4_32_1",
    "v4_32_2",
    "v4_33_0",
    "v4_33_1",
    "v4_34_0",
    "v4_34_1",
    "v4_35_0",
    "v4_36_0",
]:
    r = subprocess.run(
        [
            "gh",
            "api",
            f"repos/leanprover/reference-manual/contents/Manual/Releases/{v}.lean",
            "-H",
            "Accept: application/vnd.github.raw",
        ],
        capture_output=True,
        text=True,
    )
    (out / f"{v}.txt").write_text(r.stdout)
    print(v, r.returncode, len(r.stdout.splitlines()))
