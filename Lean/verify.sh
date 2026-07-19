#!/bin/sh
set -e
lake build
lake env lean AxiomAudit.lean
