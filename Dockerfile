# Fixed base and Debian archive snapshot. Build the full PDF environment by default.
FROM debian:bookworm-slim@sha256:3783cc01769c7b2b1b83a5c5ad96c815348e28ed7da68e2e3687004faa906251 AS compute
ENV DEBIAN_FRONTEND=noninteractive PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1 LANG=C.UTF-8 LC_ALL=C.UTF-8
RUN rm -f /etc/apt/sources.list /etc/apt/sources.list.d/* \
 && printf '%s\n' \
    'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/20260901T000000Z bookworm main' \
    'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian-security/20260901T000000Z bookworm-security main' > /etc/apt/sources.list \
 && apt-get -o Acquire::Retries=3 update \
 && apt-get install -y --no-install-recommends python3 python3-venv g++ git ca-certificates curl elan \
 && rm -rf /var/lib/apt/lists/*
RUN python3 -m venv /opt/venv
ENV PATH=/opt/venv/bin:$PATH
WORKDIR /paper
CMD ["python3", "-B", "check_environment.py", "--scope", "compute"]

FROM compute AS complete
RUN apt-get -o Acquire::Retries=3 update \
 && apt-get install -y --no-install-recommends \
    texlive-latex-base texlive-latex-recommended texlive-latex-extra \
    texlive-fonts-recommended texlive-luatex texlive-lang-japanese \
    texlive-pictures lmodern poppler-utils \
 && rm -rf /var/lib/apt/lists/*
COPY requirements-pdf.txt /opt/requirements-pdf.txt
RUN python3 -m pip install --no-cache-dir --require-hashes -r /opt/requirements-pdf.txt
CMD ["python3", "-B", "check_environment.py", "--scope", "pdf"]
