"""Deterministic OWL class/data-range simplification and negation normal form.

SPDX-License-Identifier: LGPL-3.0-or-later

The rewrite shapes follow pinned HermiT ``ExpressionManager`` at commit
37ec30aced32ac81ebecc5e33fad255ddefcb4c3, with core structural values used
directly and canonical sets replacing source/hash iteration order.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable

import pyowl_core.model as owl

_MAX_SAFE_RECURSIVE_DEPTH = 512


class UnknownExpressionError(TypeError):
    """Raised when a core model version adds an unhandled expression variant."""


class ExpressionDepthError(ValueError):
    """Raised before recursive normalization can exhaust the Python stack."""

    def __init__(self, observed: int, allowed: int) -> None:
        self.observed = observed
        self.allowed = allowed
        super().__init__(f"expression normalization depth {observed} exceeds limit {allowed}")


class ExpressionNormalizationCancelled(RuntimeError):
    """Raised cooperatively when the caller cancels expression normalization."""


class ExpressionNormalizer:
    """Normalize exact pyowl-core expressions without wrapping or mutating them."""

    __slots__ = ("_cancelled", "_max_depth", "_steps")

    def __init__(
        self,
        *,
        max_depth: int = 512,
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        if isinstance(max_depth, bool) or not isinstance(max_depth, int) or max_depth < 1:
            raise ValueError("max_depth must be a positive integer")
        if max_depth > _MAX_SAFE_RECURSIVE_DEPTH:
            raise ValueError(
                f"max_depth cannot exceed the safe/core limit {_MAX_SAFE_RECURSIVE_DEPTH}"
            )
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        self._max_depth = max_depth
        self._cancelled = cancelled
        self._steps = 0

    @property
    def steps(self) -> int:
        return self._steps

    def class_nnf(
        self,
        expression: owl.ClassExpression,
        *,
        negated: bool = False,
    ) -> owl.ClassExpression:
        if not isinstance(expression, owl.CLASS_EXPRESSION_TYPES):
            raise TypeError("expression must be a pyowl_core ClassExpression")
        if not isinstance(negated, bool):
            raise TypeError("negated must be bool")
        return self._class(expression, negated, 0)

    def data_nnf(
        self,
        data_range: owl.DataRange,
        *,
        negated: bool = False,
    ) -> owl.DataRange:
        if not isinstance(data_range, owl.DATA_RANGE_TYPES):
            raise TypeError("data_range must be a pyowl_core DataRange")
        if not isinstance(negated, bool):
            raise TypeError("negated must be bool")
        return self._data(data_range, negated, 0)

    def _checkpoint(self, depth: int) -> None:
        if depth > self._max_depth:
            raise ExpressionDepthError(depth, self._max_depth)
        self._steps += 1
        if self._steps & 0x3F == 0 and self._cancelled is not None and self._cancelled():
            raise ExpressionNormalizationCancelled("expression normalization cancelled")

    def _class(
        self,
        expression: owl.ClassExpression,
        negated: bool,
        depth: int,
    ) -> owl.ClassExpression:
        self._checkpoint(depth)
        constructor = type(expression)

        if constructor is owl.Class:
            value = expression
            assert isinstance(value, owl.Class)
            if _is_thing(value):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            if _is_nothing(value):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            return owl.ObjectComplementOf(value) if negated else value

        if constructor is owl.ObjectComplementOf:
            value = expression
            assert isinstance(value, owl.ObjectComplementOf)
            return self._class(value.operand, not negated, depth + 1)

        if constructor is owl.ObjectIntersectionOf:
            value = expression
            assert isinstance(value, owl.ObjectIntersectionOf)
            operands = (self._class(operand, negated, depth + 1) for operand in value.operands)
            return _class_union(operands) if negated else _class_intersection(operands)

        if constructor is owl.ObjectUnionOf:
            value = expression
            assert isinstance(value, owl.ObjectUnionOf)
            operands = (self._class(operand, negated, depth + 1) for operand in value.operands)
            return _class_intersection(operands) if negated else _class_union(operands)

        if constructor is owl.ObjectOneOf:
            value = expression
            assert isinstance(value, owl.ObjectOneOf)
            return owl.ObjectComplementOf(value) if negated else value

        if constructor is owl.ObjectHasValue:
            value = expression
            assert isinstance(value, owl.ObjectHasValue)
            object_expanded = owl.ObjectSomeValuesFrom(
                value.property,
                owl.ObjectOneOf(owl.CanonicalSet((value.value,))),
            )
            return self._class(object_expanded, negated, depth + 1)

        if constructor is owl.DataHasValue:
            value = expression
            assert isinstance(value, owl.DataHasValue)
            data_expanded = owl.DataSomeValuesFrom(
                (value.property,),
                owl.DataOneOf(owl.CanonicalSet((value.value,))),
            )
            return self._class(data_expanded, negated, depth + 1)

        if constructor is owl.ObjectSomeValuesFrom:
            value = expression
            assert isinstance(value, owl.ObjectSomeValuesFrom)
            if _is_bottom_object_property(value.property):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            filler = self._class(value.filler, negated, depth + 1)
            if negated:
                return _object_all(value.property, filler)
            return _object_some(value.property, filler)

        if constructor is owl.ObjectAllValuesFrom:
            value = expression
            assert isinstance(value, owl.ObjectAllValuesFrom)
            if _is_bottom_object_property(value.property):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            filler = self._class(value.filler, negated, depth + 1)
            if negated:
                return _object_some(value.property, filler)
            return _object_all(value.property, filler)

        if constructor is owl.ObjectHasSelf:
            value = expression
            assert isinstance(value, owl.ObjectHasSelf)
            if _is_bottom_object_property(value.property):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            if _is_top_object_property(value.property):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            return owl.ObjectComplementOf(value) if negated else value

        if constructor is owl.ObjectMinCardinality:
            value = expression
            assert isinstance(value, owl.ObjectMinCardinality)
            filler = self._class(value.filler, False, depth + 1)
            if value.cardinality == 0 or _is_bottom_object_property(value.property):
                base = owl.OWL_THING if value.cardinality == 0 else owl.OWL_NOTHING
                return _negate_builtin(base) if negated else base
            if _is_nothing(filler):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            if negated:
                if value.cardinality == 1:
                    complement = self._class(value.filler, True, depth + 1)
                    return _object_all(value.property, complement)
                return _object_max(value.cardinality - 1, value.property, filler)
            if value.cardinality == 1:
                return _object_some(value.property, filler)
            return owl.ObjectMinCardinality(value.cardinality, value.property, filler)

        if constructor is owl.ObjectMaxCardinality:
            value = expression
            assert isinstance(value, owl.ObjectMaxCardinality)
            filler = self._class(value.filler, False, depth + 1)
            if _is_bottom_object_property(value.property) or _is_nothing(filler):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            if negated:
                return _object_min(value.cardinality + 1, value.property, filler)
            if value.cardinality == 0:
                complement = self._class(value.filler, True, depth + 1)
                return _object_all(value.property, complement)
            return _object_max(value.cardinality, value.property, filler)

        if constructor is owl.ObjectExactCardinality:
            value = expression
            assert isinstance(value, owl.ObjectExactCardinality)
            filler = self._class(value.filler, False, depth + 1)
            if _is_bottom_object_property(value.property) or _is_nothing(filler):
                base = owl.OWL_THING if value.cardinality == 0 else owl.OWL_NOTHING
                return _negate_builtin(base) if negated else base
            if negated:
                if value.cardinality == 0:
                    return _object_min(1, value.property, filler)
                object_lower = (
                    _object_all(
                        value.property,
                        self._class(value.filler, True, depth + 1),
                    )
                    if value.cardinality == 1
                    else _object_max(value.cardinality - 1, value.property, filler)
                )
                return _class_union(
                    (
                        object_lower,
                        _object_min(value.cardinality + 1, value.property, filler),
                    )
                )
            if value.cardinality == 0:
                complement = self._class(value.filler, True, depth + 1)
                return _object_all(value.property, complement)
            return _class_intersection(
                (
                    _object_min(value.cardinality, value.property, filler),
                    _object_max(value.cardinality, value.property, filler),
                )
            )

        if constructor is owl.DataSomeValuesFrom:
            value = expression
            assert isinstance(value, owl.DataSomeValuesFrom)
            if any(_is_bottom_data_property(prop) for prop in value.properties):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            data_filler = self._data(value.filler, negated, depth + 1)
            if negated:
                return _data_all(value.properties, data_filler)
            return _data_some(value.properties, data_filler)

        if constructor is owl.DataAllValuesFrom:
            value = expression
            assert isinstance(value, owl.DataAllValuesFrom)
            if any(_is_bottom_data_property(prop) for prop in value.properties):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            data_filler = self._data(value.filler, negated, depth + 1)
            if negated:
                return _data_some(value.properties, data_filler)
            return _data_all(value.properties, data_filler)

        if constructor is owl.DataMinCardinality:
            value = expression
            assert isinstance(value, owl.DataMinCardinality)
            data_filler = self._data(value.filler, False, depth + 1)
            if value.cardinality == 0 or _is_bottom_data_property(value.property):
                base = owl.OWL_THING if value.cardinality == 0 else owl.OWL_NOTHING
                return _negate_builtin(base) if negated else base
            if _is_bottom_data_range(data_filler):
                return owl.OWL_THING if negated else owl.OWL_NOTHING
            if negated:
                if value.cardinality == 1:
                    data_complement = self._data(value.filler, True, depth + 1)
                    return _data_all((value.property,), data_complement)
                return _data_max(value.cardinality - 1, value.property, data_filler)
            if value.cardinality == 1:
                return _data_some((value.property,), data_filler)
            return owl.DataMinCardinality(value.cardinality, value.property, data_filler)

        if constructor is owl.DataMaxCardinality:
            value = expression
            assert isinstance(value, owl.DataMaxCardinality)
            data_filler = self._data(value.filler, False, depth + 1)
            if _is_bottom_data_property(value.property) or _is_bottom_data_range(data_filler):
                return owl.OWL_NOTHING if negated else owl.OWL_THING
            if negated:
                return _data_min(value.cardinality + 1, value.property, data_filler)
            if value.cardinality == 0:
                data_complement = self._data(value.filler, True, depth + 1)
                return _data_all((value.property,), data_complement)
            return _data_max(value.cardinality, value.property, data_filler)

        if constructor is owl.DataExactCardinality:
            value = expression
            assert isinstance(value, owl.DataExactCardinality)
            data_filler = self._data(value.filler, False, depth + 1)
            if _is_bottom_data_property(value.property) or _is_bottom_data_range(data_filler):
                base = owl.OWL_THING if value.cardinality == 0 else owl.OWL_NOTHING
                return _negate_builtin(base) if negated else base
            if negated:
                if value.cardinality == 0:
                    return _data_min(1, value.property, data_filler)
                data_lower = (
                    _data_all(
                        (value.property,),
                        self._data(value.filler, True, depth + 1),
                    )
                    if value.cardinality == 1
                    else _data_max(value.cardinality - 1, value.property, data_filler)
                )
                return _class_union(
                    (
                        data_lower,
                        _data_min(value.cardinality + 1, value.property, data_filler),
                    )
                )
            if value.cardinality == 0:
                data_complement = self._data(value.filler, True, depth + 1)
                return _data_all((value.property,), data_complement)
            return _class_intersection(
                (
                    _data_min(value.cardinality, value.property, data_filler),
                    _data_max(value.cardinality, value.property, data_filler),
                )
            )

        raise UnknownExpressionError(f"unhandled class expression: {constructor.__name__}")

    def _data(
        self,
        data_range: owl.DataRange,
        negated: bool,
        depth: int,
    ) -> owl.DataRange:
        self._checkpoint(depth)
        constructor = type(data_range)
        if constructor in {owl.Datatype, owl.DataOneOf, owl.DatatypeRestriction}:
            if negated:
                if _is_top_data_range(data_range):
                    return _bottom_data_range()
                return owl.DataComplementOf(data_range)
            return data_range
        if constructor is owl.DataComplementOf:
            value = data_range
            assert isinstance(value, owl.DataComplementOf)
            return self._data(value.operand, not negated, depth + 1)
        if constructor is owl.DataIntersectionOf:
            value = data_range
            assert isinstance(value, owl.DataIntersectionOf)
            operands = (self._data(item, negated, depth + 1) for item in value.operands)
            return _data_union(operands) if negated else _data_intersection(operands)
        if constructor is owl.DataUnionOf:
            value = data_range
            assert isinstance(value, owl.DataUnionOf)
            operands = (self._data(item, negated, depth + 1) for item in value.operands)
            return _data_intersection(operands) if negated else _data_union(operands)
        raise UnknownExpressionError(f"unhandled data range: {constructor.__name__}")


def _class_intersection(values: Iterable[owl.ClassExpression]) -> owl.ClassExpression:
    flattened: list[owl.ClassExpression] = []
    for value in values:
        if _is_nothing(value):
            return owl.OWL_NOTHING
        if _is_thing(value):
            continue
        if isinstance(value, owl.ObjectIntersectionOf):
            flattened.extend(value.operands)
        else:
            flattened.append(value)
    operands = owl.CanonicalSet(flattened)
    if not operands:
        return owl.OWL_THING
    if len(operands) == 1:
        return next(iter(operands))
    return owl.ObjectIntersectionOf(operands)


def _class_union(values: Iterable[owl.ClassExpression]) -> owl.ClassExpression:
    flattened: list[owl.ClassExpression] = []
    for value in values:
        if _is_thing(value):
            return owl.OWL_THING
        if _is_nothing(value):
            continue
        if isinstance(value, owl.ObjectUnionOf):
            flattened.extend(value.operands)
        else:
            flattened.append(value)
    operands = owl.CanonicalSet(flattened)
    if not operands:
        return owl.OWL_NOTHING
    if len(operands) == 1:
        return next(iter(operands))
    return owl.ObjectUnionOf(operands)


def _data_intersection(values: Iterable[owl.DataRange]) -> owl.DataRange:
    flattened: list[owl.DataRange] = []
    for value in values:
        if _is_bottom_data_range(value):
            return _bottom_data_range()
        if _is_top_data_range(value):
            continue
        if isinstance(value, owl.DataIntersectionOf):
            flattened.extend(value.operands)
        else:
            flattened.append(value)
    operands = owl.CanonicalSet(flattened)
    if not operands:
        return owl.RDFS_LITERAL
    if len(operands) == 1:
        return next(iter(operands))
    return owl.DataIntersectionOf(operands)


def _data_union(values: Iterable[owl.DataRange]) -> owl.DataRange:
    flattened: list[owl.DataRange] = []
    for value in values:
        if _is_top_data_range(value):
            return owl.RDFS_LITERAL
        if _is_bottom_data_range(value):
            continue
        if isinstance(value, owl.DataUnionOf):
            flattened.extend(value.operands)
        else:
            flattened.append(value)
    operands = owl.CanonicalSet(flattened)
    if not operands:
        return _bottom_data_range()
    if len(operands) == 1:
        return next(iter(operands))
    return owl.DataUnionOf(operands)


def _object_some(
    property: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
) -> owl.ClassExpression:
    if _is_nothing(filler) or _is_bottom_object_property(property):
        return owl.OWL_NOTHING
    return owl.ObjectSomeValuesFrom(property, filler)


def _object_all(
    property: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
) -> owl.ClassExpression:
    if _is_thing(filler) or _is_bottom_object_property(property):
        return owl.OWL_THING
    return owl.ObjectAllValuesFrom(property, filler)


def _object_min(
    cardinality: int,
    property: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
) -> owl.ClassExpression:
    if cardinality == 0:
        return owl.OWL_THING
    if cardinality == 1:
        return _object_some(property, filler)
    return owl.ObjectMinCardinality(cardinality, property, filler)


def _object_max(
    cardinality: int,
    property: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
) -> owl.ClassExpression:
    if _is_nothing(filler) or _is_bottom_object_property(property):
        return owl.OWL_THING
    return owl.ObjectMaxCardinality(cardinality, property, filler)


def _data_some(
    properties: tuple[owl.DataProperty, ...],
    filler: owl.DataRange,
) -> owl.ClassExpression:
    if _is_bottom_data_range(filler) or any(_is_bottom_data_property(prop) for prop in properties):
        return owl.OWL_NOTHING
    return owl.DataSomeValuesFrom(properties, filler)


def _data_all(
    properties: tuple[owl.DataProperty, ...],
    filler: owl.DataRange,
) -> owl.ClassExpression:
    if _is_top_data_range(filler) or any(_is_bottom_data_property(prop) for prop in properties):
        return owl.OWL_THING
    return owl.DataAllValuesFrom(properties, filler)


def _data_min(
    cardinality: int,
    property: owl.DataProperty,
    filler: owl.DataRange,
) -> owl.ClassExpression:
    if cardinality == 0:
        return owl.OWL_THING
    if cardinality == 1:
        return _data_some((property,), filler)
    return owl.DataMinCardinality(cardinality, property, filler)


def _data_max(
    cardinality: int,
    property: owl.DataProperty,
    filler: owl.DataRange,
) -> owl.ClassExpression:
    if _is_bottom_data_range(filler) or _is_bottom_data_property(property):
        return owl.OWL_THING
    return owl.DataMaxCardinality(cardinality, property, filler)


def _negate_builtin(expression: owl.ClassExpression) -> owl.ClassExpression:
    return owl.OWL_NOTHING if _is_thing(expression) else owl.OWL_THING


def _bottom_data_range() -> owl.DataComplementOf:
    return owl.DataComplementOf(owl.RDFS_LITERAL)


def _is_thing(expression: owl.ClassExpression) -> bool:
    return isinstance(expression, owl.Class) and expression.iri.value == owl.OWL_THING.iri.value


def _is_nothing(expression: owl.ClassExpression) -> bool:
    return isinstance(expression, owl.Class) and expression.iri.value == owl.OWL_NOTHING.iri.value


def _is_top_data_range(data_range: owl.DataRange) -> bool:
    return (
        isinstance(data_range, owl.Datatype) and data_range.iri.value == owl.RDFS_LITERAL.iri.value
    )


def _is_bottom_data_range(data_range: owl.DataRange) -> bool:
    return isinstance(data_range, owl.DataComplementOf) and _is_top_data_range(data_range.operand)


def _is_top_object_property(property: owl.ObjectPropertyExpression) -> bool:
    named = property.property if isinstance(property, owl.ObjectInverseOf) else property
    return named.iri.value == owl.OWL_TOP_OBJECT_PROPERTY.iri.value


def _is_bottom_object_property(property: owl.ObjectPropertyExpression) -> bool:
    named = property.property if isinstance(property, owl.ObjectInverseOf) else property
    return named.iri.value == owl.OWL_BOTTOM_OBJECT_PROPERTY.iri.value


def _is_bottom_data_property(property: owl.DataProperty) -> bool:
    return property.iri.value == owl.OWL_BOTTOM_DATA_PROPERTY.iri.value


__all__ = [
    "ExpressionDepthError",
    "ExpressionNormalizationCancelled",
    "ExpressionNormalizer",
    "UnknownExpressionError",
]
