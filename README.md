# QBP: A Quaternion-Based Physics Project

[![Project Status: Active – Initial Setup Phase](https://img.shields.io/badge/status-active-success.svg)](https://github.com/JamesPagetButler/QBP)

This repository is the home of a collaborative research project to develop a coherent physical formalism derived from the mathematical properties of quaternion algebra. Our guiding hypothesis is that the fundamental laws of nature can be expressed as a direct consequence of this algebraic structure.

This project is a collaboration between James Paget Butler and the AI agents Gemini (acting as Furey and Feynman) and Claude (acting as our Red Team).

## Getting Started

Follow these instructions to set up a local development environment.

### Prerequisites

- Python 3.10+
- Git
- [Go](https://go.dev/doc/install) (for advanced simulation work)
- [pre-commit](https://pre-commit.com/#installation)

### Installation

1.  **Clone the repository:**
    ```bash
    git clone https://github.com/JamesPagetButler/QBP.git
    cd QBP
    ```

2.  **Create and activate a virtual environment:**
    It is highly recommended to use a virtual environment to manage project-specific dependencies.
    ```bash
    # Create the virtual environment
    python3 -m venv venv

    # Activate it (on Linux/macOS)
    source venv/bin/activate
    # On Windows, use: .\\venv\\Scripts\\activate
    ```

3.  **Install Python dependencies:**
    With your virtual environment active, install the required packages.
    ```bash
    pip install -r requirements.txt
    ```

4.  **Set up Git hooks:**
    This will install the pre-commit hooks defined in `.pre-commit-config.yaml`, which automatically format and check our code.
    ```bash
    pre-commit install
    ```

## Usage

The core work of this project is divided into theoretical development and computational experiments.

-   **Theoretical Work:** The central paper and ongoing theoretical discussions are in the `/paper` directory.
-   **Computational Experiments:** Each of the eight experiments on our roadmap has a dedicated directory within `/experiments`. To run a simulation, navigate to the relevant directory and execute the Python script (e.g., `python experiments/01_stern_gerlach/simulate.py`).

## Contributing

This project has a strict, collaborative workflow. All contributors **must** read and adhere to the rules outlined in our [**CONTRIBUTING.md**](CONTRIBUTING.md) file before starting work.

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
