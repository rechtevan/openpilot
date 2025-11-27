# Configuration file for Sphinx documentation builder
# Requirements traceability for openpilot formal verification

project = 'openpilot Requirements Traceability'
copyright = '2024, rechtevan'
author = 'rechtevan'

extensions = [
    'sphinx_needs',
    'sphinxcontrib.plantuml',  # For diagrams
    'myst_parser',  # For markdown support
]

# Sphinx-needs configuration
needs_types = [
    # Upstream requirements (from comma.ai docs)
    dict(directive="req", title="Requirement", prefix="REQ-", color="#BFD8D2", style="node"),

    # Specifications derived from requirements
    dict(directive="spec", title="Specification", prefix="SPEC-", color="#FEDCD2", style="node"),

    # Formal verification artifacts
    dict(directive="verify", title="Verification", prefix="VER-", color="#DCB8CB", style="node"),

    # Test cases
    dict(directive="test", title="Test", prefix="TEST-", color="#DF744A", style="node"),

    # Implementation references
    dict(directive="impl", title="Implementation", prefix="IMPL-", color="#C9E4CA", style="node"),
]

# Link types for traceability
needs_extra_links = [
    {
        "option": "derives_from",
        "incoming": "derived_by",
        "copy": False,
    },
    {
        "option": "verifies",
        "incoming": "verified_by",
        "copy": False,
    },
    {
        "option": "implements",
        "incoming": "implemented_by",
        "copy": False,
    },
    {
        "option": "tests",
        "incoming": "tested_by",
        "copy": False,
    },
    {
        "option": "traces_to",
        "incoming": "traced_from",
        "copy": False,
    },
]

# Extra options for needs (status is built-in, don't redefine)
needs_extra_options = [
    "upstream_source",      # Link to upstream document
    "upstream_section",     # Section in upstream doc
    "standard",             # ISO/MISRA standard reference
    "priority",             # Priority level
    "verification_method",  # How it's verified (formal, test, review, analysis)
]

# ID regex pattern
needs_id_regex = "^[A-Z]+-[A-Z]+-[0-9]+"

# Build settings
templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']
html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']

# Source file settings
source_suffix = {
    '.rst': 'restructuredtext',
    '.md': 'markdown',
}

# PlantUML for diagrams (optional)
# plantuml = 'java -jar /path/to/plantuml.jar'
