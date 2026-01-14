fn main(point1:  std::embedded_curve_ops::EmbeddedCurvePoint, point2:  std::embedded_curve_ops::EmbeddedCurvePoint) -> pub std::embedded_curve_ops::EmbeddedCurvePoint  {
    let result = std::embedded_curve_ops::embedded_curve_add(point1, point2);
    result
}

