"""Load BART-MNLI once and score one entailment direction."""

from __future__ import annotations

from functools import lru_cache

def available() -> bool:
    try:
        import torch  
        import transformers  
    except ImportError:
        return False
    return True


@lru_cache(maxsize=2)
def load(model_name: str):
    import torch
    from transformers import AutoModelForSequenceClassification, AutoTokenizer

    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForSequenceClassification.from_pretrained(model_name)
    device = "cuda" if torch.cuda.is_available() else (
        "mps" if torch.backends.mps.is_available() else "cpu"
    )
    model.eval().to(device)
    labels = {label.lower(): int(index) for index, label in model.config.id2label.items()}
    return tokenizer, model, device, labels


def score(premise: str, hypothesis: str, model_name: str) -> dict[str, float | str]:
    import torch

    tokenizer, model, device, labels = load(model_name)
    inputs = tokenizer(premise, hypothesis, return_tensors="pt", truncation=False)
    token_count = int(inputs["input_ids"].shape[-1])
    token_limit = min(tokenizer.model_max_length, model.config.max_position_embeddings)
    if token_count > token_limit:
        raise ValueError(
            f"full NLI pair has {token_count} tokens, above {model_name}'s "
            f"{token_limit}-token limit; input was not split or truncated"
        )
    inputs = inputs.to(device)
    with torch.no_grad():
        probabilities = torch.softmax(model(**inputs).logits[0], dim=-1).tolist()

    def probability(label: str) -> float:
        index = labels.get(label)
        return float(probabilities[index]) if index is not None else 0.0

    values = {name: probability(name) for name in ("entailment", "neutral", "contradiction")}
    values["label"] = max(values, key=values.get)
    return values
