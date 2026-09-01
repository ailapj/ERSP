"""Compare x and the final x-prime with the paper's NLI decision tree."""

from __future__ import annotations

from nli import start


DRIFT = {"Unrelated", "Contradiction"}


# 6 classification defined by the paper
# x -> x' e_forward / contraditcion
# x <- x' e_backward / contradiction
def classify(forward: dict, backward: dict) -> str:
    e_forward = float(forward["entailment"])
    e_backward = float(backward["entailment"])
    e_min = min(e_forward, e_backward)
    c_max = max(float(forward["contradiction"]), float(backward["contradiction"]))
    if c_max >= 0.6:
        return "Contradiction"
    if e_min >= 0.7 and c_max < 0.2:
        return "Equivalent"
    if e_forward >= 0.6 and e_backward < 0.4:
        return "Strengthened"
    if e_backward >= 0.6 and e_forward < 0.4:
        return "Weakened"
    if e_min >= 0.3 and c_max < 0.3:
        return "Related"
    return "Unrelated"


# main entrance
def compare(original: str, reconstructed: str, model_name: str) -> dict:
    if not start.available():
        return {
            "available": False,
            "category": None,
            "drift": None,
            "note": "torch/transformers are not installed",
    }
    try:
        forward = start.score(original, reconstructed, model_name)
        backward = start.score(reconstructed, original, model_name)
    except Exception as error:
        return {
            "available": False,
            "category": None,
            "drift": None,
            "note": str(error),
        }
    category = classify(forward, backward)
    return {
        "available": True,
        "category": category,
        "drift": category in DRIFT,
        "forward": forward,
        "backward": backward,
        "note": "post-hoc signal only",
    }
