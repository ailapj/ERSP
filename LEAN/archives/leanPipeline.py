from anthropic import Anthropic
from dotenv import load_dotenv
import subprocess
import os
from pathlib import Path
import re

CANDIDATE_PATH = "candidate.lean"
REFERENCE_PATH = "Tutorial/Lean/moduleOneRevised.lean"
with open(REFERENCE_PATH, "r") as f:
            REFERENCE_SPEC = f.read()

load_dotenv()
client = Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))

# Calling Claude with the prompt 
def call_claude(prompt, max_new_tokens=4000, temperature=0.7):
    message = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=max_new_tokens, # how long the response can be (one token is roughly 4 characters, so 200 tokens is about 800 characters)
        temperature=temperature, # randomness (0 = deterministic, higher temperature = more random)
        messages=[
            {"role": "user", "content": prompt}
        ],
    )
    # writing the claude outputs in log.txt to keep track
    with open("ai_log.txt", "a") as f:
        f.write(message.content[0].text + "\n\n" + "="*60 + "\n\n")

    return message.content[0].text

# Extract only the lean code from the generated response  
def extract_lean_code(response_text):
    # searches for the '''lean ''' 
    match = re.search(
        r"```(?:lean)?\s*\n(.*?)```",
        response_text,
        re.DOTALL | re.IGNORECASE,
    )
    if match:
        return match.group(1).strip()
    return response_text.strip()

# Ensures that the given proof is not trivial (true if sound, false if too simple)
def sound_proof(response_text) -> bool:
    # make sure the given proof does not contain forbidden words 
    forbidden = [
        r"\bsorry\b"
    ]
    pattern = r"\b( " + "|".join(forbidden) + r")\b"
    return re.search(pattern, response_text) is None  


# Save the argument content to a file at the specified path and return the path.
def save_file(content, file_path):
    with open(file_path, "w", encoding="utf-8") as f:
        f.write(content)
    return file_path


# Run Lean on the given file path and return a tuple of (return code, stdou, stderr).
# returncode = 0 --> success, =1 --> some error
# stdout captures: file path, errors, goal diagnostics, = null if returncode is 0 
# stderr is null if returncode is 0
def run_lean(lean_file):
    lean_file = os.path.abspath(lean_file)
    result = subprocess.run(
        ["lake", "env", "lean", lean_file],
        capture_output=True,
        text=True
    )
    return result.returncode, result.stdout, result.stderr


# Helper function that implements a loop to repair syntax errors in the generated Lean code.
def repair_syntax_loop(max_attempts=5):
    for attempt in range(max_attempts):
        print(f"\n[Syntax Attempt {attempt+1}]")

        returncode, stdout, stderr = run_lean(CANDIDATE_PATH)

        print(stdout)

        # If there are no syntax errors, we can exit the loop and proceed to logic repair.
        if returncode == 0:
            return True

        # If there is a syntax error, we will prompt the LLM to fix only the candidate plan.
        with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
            candidate_code = f.read()

        prompt = f"""
Fix this Lean code so it compiles.

Rules: 
- Only use the information directly given by user about the patient information 
- Do not use trivially correct proofs. (e.g. 'sorry') 
Current:
{candidate_code}

Error:
stdout of Lean: {stdout}\
stderr of Lean: {stderr}
"""     
        # generate the plan with the prompt
        generated_plan = call_claude(prompt, temperature=0)
        # exrtact the Lean code portion of the LLM response
        lean_code = extract_lean_code(generated_plan) 
        # save the Lean code to candidate_path
        save_file(lean_code, CANDIDATE_PATH)

    # If we exhaust all attempts without success, return False to indicate failure.
    return False


# Helper function that implements a loop to repair logic errors and get a safe plan. 
# Also ensures that the plan is not trivially true or too simple 

def repair_logic_loop(max_attempts=5):
    for attempt in range(max_attempts):
        print(f"\n[Logic Attempt {attempt+1}]")
        # Run the Lean code to capture the diagnostics and return values 
        returncode, stdout, stderr = run_lean(CANDIDATE_PATH)
        print(stdout)

        with open(CANDIDATE_PATH, "r") as f:
            candidate_code = f.read()
        # Check to make sure the plan is sound and not too simple
        if not sound_proof(candidate_code) : 
            prompt = "The proof was rejected due to being trivially true and too simple.\n"
        else : 
            if returncode == 0:
                print("SAFE and SOUND: No violating instance exists.")
                return True
        #if plan becomes uncompilable, we need to go back to syntax repair loop to fix it before we can continue logic repair.
        if (returncode == 1):
            print("Syntax error detected during logic repair. Switching back to syntax repair.")
            if not repair_syntax_loop():
                print("Failed to repair syntax during logic repair.")
                return False
            continue

        prompt += f"""
You are repairing a Lean plan.

The theorem that the candidate plan is safe is not proven 

GOAL:
Modify the candidate plan so that the proof of its safety is provable. Then prove it. 

RULES:
- Only use variables, signatures, and fields already defined in the file below. Do NOT invent new names.
- Do not use trivillay correct proofs (e.g. 'sorry') 

Reference code: 
{REFERENCE_SPEC}

Current plan:
{candidate_code}

Lean stdout output:
{stdout}
Lean stderr output: 
{stderr}
"""

        generated_plan = call_claude(prompt, temperature=0)
        save_file(generated_plan, CANDIDATE_PATH)

    # If we exhaust all attempts without success, return False to indicate failure.
    return False


# The first generation step where we prompt the LLM to generate a plan from scratch based on the user prompt. 
def generate_plan(user_prompt):
    with open(CANDIDATE_PATH, "r") as f:
            candidate_code = f.read()

    prompt = f"""
You have been given a medial scenario: {user_prompt}

GOAL: 
produce the correct answer in Lean and prove its correctness. 

Here is the LEAN CONSTRAINTS AND PROCEDURE (this will NOT be modified):
{REFERENCE_SPEC}

RULES: 
- Use ONLY variables, signatures, and fields already defined in the file below
- Do NOT invent new names
- Your entire response should be a compilable Lean code. Put any thoughts and planning in the comments of Lean code. 

WHAT YOU WILL BE MODIFYING (you will define the plan and prove it): 
{candidate_code} 
"""

    return call_claude(prompt, temperature=0.7)


# The full pipeline of generating the initial plan, repairing syntax errors , then repairing logic errors if the generated plan is not safe

def generate_and_verify(user_prompt, rounds=1):
    for i in range(rounds):
        print(f"\n == Pipleline round {i+1} ==")

        # generate plan
        generated_response = generate_plan(user_prompt)

        save_file(generated_response, CANDIDATE_PATH)

        # syntax phase
        if not repair_syntax_loop():
            print("Failed syntax repair")
            continue

        # logic phase
        if repair_logic_loop():
            print("SAFE PLAN VERIFIED")
            return True

    print("Failed to produce safe plan")
    return False


# ------------------ Main ------------------

def main():
    prompt = """
What should you do if the child has a priority sign?
"""

    generate_and_verify(prompt)


if __name__ == "__main__":
    main()