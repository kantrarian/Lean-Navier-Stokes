#!/usr/bin/env python3
"""
Test connection to LM Studio / DeepSeek Prover
"""

from openai import OpenAI
import requests

print("="*80)
print("LM Studio Connection Diagnostic")
print("="*80)

# Ports to test
ports = [1234, 36798, 1235, 8000, 8080]

for port in ports:
    print(f"\nTesting port {port}...")

    # Test 1: Basic HTTP connection
    try:
        response = requests.get(f"http://localhost:{port}/v1/models", timeout=2)
        print(f"  [OK] HTTP connection successful on port {port}")
        print(f"  Status code: {response.status_code}")
        if response.status_code == 200:
            print(f"  Response: {response.json()}")
    except requests.exceptions.ConnectionError:
        print(f"  [FAIL] Connection refused on port {port}")
    except requests.exceptions.Timeout:
        print(f"  [FAIL] Connection timeout on port {port}")
    except Exception as e:
        print(f"  [ERROR] {e}")

    # Test 2: OpenAI client
    try:
        client = OpenAI(base_url=f"http://localhost:{port}/v1", api_key="test")
        models = client.models.list()
        print(f"  [OK] OpenAI client works on port {port}")
        print(f"  Available models: {[m.id for m in models.data]}")
    except Exception as e:
        print(f"  [FAIL] OpenAI client error: {type(e).__name__}")

print("\n" + "="*80)
print("INSTRUCTIONS:")
print("="*80)
print("""
1. Make sure LM Studio is running
2. In LM Studio, go to the 'Local Server' tab (or 'Developer' tab)
3. Click 'Start Server' if it's not already running
4. Note the port number shown (usually 1234)
5. Make sure 'deepseek-prover-v2-7b' model is loaded
6. Re-run this diagnostic to confirm connection

If you see a working port above, update run_sprint.py:
  LM_STUDIO_PORT = <working_port>
""")
print("="*80)
