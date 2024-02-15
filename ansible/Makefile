# Makefile

.PHONY: setup run all

# Setup the virtual environment and install Ansible
setup:
	@echo "Creating virtual environment..."
	python3 -m venv venv
	@echo "Activating virtual environment and installing Ansible..."
	. venv/bin/activate && \
		venv/bin/python3 -m pip install --upgrade pip && \
		pip install ansible

# Run the Ansible playbook
run:
	@echo "Running Ansible playbook..."
	venv/bin/ansible-playbook -i ./inventory playbook.yml

check:
	@echo "Running Ansible playbook..."
	venv/bin/ansible-playbook -i ./inventory playbook.yml --check -vv

# Default target
all: setup run
