"""
QBP Test Configuration

This file configures pytest for the QBP project.
All tests follow Rule 5: Link Tests to Reality.
"""

import sys
from pathlib import Path

import pytest
import numpy as np

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))


@pytest.fixture
def tolerance():
    """Standard numerical tolerance for physics calculations."""
    return 1e-10


@pytest.fixture
def pi():
    """Pi constant for angle calculations."""
    return np.pi
