import Mathlib

/-!
**FR.** Résultat purement normique contrôlant la variation de norme carrée par
la distance entre vecteurs ; il ne porte aucune interprétation quantique.

**EN.** Purely norm-theoretic result controlling squared-norm variation by
vector distance; it carries no quantum interpretation.
-/

namespace EverettianDecoherence.Metrics

theorem abs_norm_sq_sub_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| = |(‖u‖ + ‖v‖) * (‖u‖ - ‖v‖)| := by
      rw [← sq_sub_sq]
    _ = (‖u‖ + ‖v‖) * |‖u‖ - ‖v‖| := by
      rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ :=
      mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

end EverettianDecoherence.Metrics
