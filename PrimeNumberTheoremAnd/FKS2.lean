import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.BKLNW
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Tactic.NormNum.NatFactorial

blueprint_comment /--
\section{The implications of FKS2}

In this file we record the implications in the paper \cite{FKS2} that allow one to convert primary bounds on $E_\psi$ into secondary bounds on $E_\pi$, $E_\theta$.
-/

open Real

namespace FKS2

@[blueprint
  "fks2-rem"
  (title := "Remark in FKS2 Section 1.1")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows directly from the definitions of $\li$ and $\Li$. -/)
  (latexEnv := "remark")]
theorem sec_1_1_remark : ∀ x > 2, li x - Li x = li 2 := sorry

@[blueprint
  "fks2-eq-16"
  (title := "g function, FKS2 (16)")
  (statement := /--
  For any $a,b,c,x \in \mathbb{R}$ we define
  $g(a,b,c,x) := x^{-a} (\log x)^b \exp( c (\log x)^{1/2} )$. -/)]
noncomputable def g_bound (a b c x : ℝ) : ℝ := x^(-a) * (log x)^b * exp (c * (log x)^(1/2))

@[blueprint
  "fks2-eq-17"
  (title := "FKS2 equation (17)")
  (statement := /--
  For any $2 \leq x_0 < x$ one has
  $$ (\pi(x) - \Li(x)) - (\pi(x_0) - \Li(x_0)) = \frac{\theta(x) - x}{\log x}
    - \frac{\theta(x_0) - x_0}{\log x_0} + \int_{x_0}^x \frac{\theta(t) - t}{t \log^2 t} dt.$$ -/)
  (proof := /-- This follows from Sublemma \ref{rs-417}. -/)
  (latexEnv := "sublemma")]
theorem eq_17 {x₀ x : ℝ} (hx₀ : x₀ ≥ 2) (hx : x > x₀) :
  (pi x - Li x) - (pi x₀ - Li x₀) =
    (θ x - x) / log x - (θ x₀ - x₀) / log x₀ +
    ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) :=
  sorry

@[blueprint
  "fks2-lemma-10-substep"
  (title := "FKS2 Sublemma 10-1")
  (statement := /-- We have
$$ \frac{d}{dx} g(a, b, c, x) = \left( -a \log(x) + b + \frac{c}{2}\sqrt{\log(x)} \right) x^{-a-1} (\log(x))^{b-1} \exp(c\sqrt{\log(x)}).$$
  -/)
  (proof := /-- This follows from straightforward differentiation. -/)
  (latexEnv := "sublemma")]
theorem lemma_10_substep {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x =
    (-a * log x + b + (c / 2) * sqrt (log x)) * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) :=
  sorry

@[blueprint
  "fks2-lemma-10-substep-2"
  (title := "FKS2 Sublemma 10-2")
  (statement := /-- $\frac{d}{dx} g(a, b, c, x) $ is negative when $-au^2 + \frac{c}{2}u + b < 0$, where $u = \sqrt{\log(x)}$.
  -/)
  (proof := /-- Clear from previous sublemma. -/)
  (latexEnv := "sublemma")]
theorem lemma_10_substep_2 {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x < 0 ↔
    -a * (sqrt (log x)) ^ 2 + (c / 2) * sqrt (log x) + b < 0 := by
  have hlogx := log_pos hx
  rw [lemma_10_substep hx, sq_sqrt hlogx.le]
  have hpos : 0 < x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) := by positivity
  rw [show ∀ y, y * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) =
      y * (x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x))) from fun _ => by ring]
  rw [mul_neg_iff]
  constructor <;> intro h
  · rcases h with ⟨-, hc⟩ | ⟨h, -⟩ <;> linarith
  · exact Or.inr ⟨by linarith, hpos⟩

@[blueprint
  "fks2-lemma-10a"
  (title := "FKS2 Lemma 10a")
  (statement := /-- If $a>0$, $c>0$ and $b < -c^2/16a$, then $g(a,b,c,x)$ decreases with $x$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. There are no roots when $b < -\frac{c^2}{16a}$, and the derivative is always negative in this case.
 -/)
  (latexEnv := "lemma")]
theorem lemma_10a {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b < -c ^ 2 / (16 * a)) :
  StrictAnti (g_bound a b c) :=
  sorry

@[blueprint
  "fks2-lemma-10b"
  (title := "FKS2 Lemma 10b")
  (statement := /--
  For any $a>0$, $c>0$ and $b \geq -c^2/16a$, $g(a,b,c,x)$ decreases with $x$ for
  $x > \exp((\frac{c}{4a} + \frac{1}{2a} \sqrt{\frac{c^2}{4} + 4ab})^2)$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a > 0$, there are two real roots only if $\frac{c^2}{4} + 4ab \geq 0$ or equivalently $b \geq -\frac{c^2}{16a}$, and the derivative is negative for $u > \frac{\frac{c}{2} + \sqrt{\frac{c^2}{4} + 4ab}}{2a}$.
 -/)
  (latexEnv := "lemma")]
theorem lemma_10b {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b ≥ -c ^ 2 / (16 * a)) :
    StrictAntiOn (g_bound a b c)
      (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) :=
  sorry

@[blueprint
  "fks2-lemma-10c"
  (title := "FKS2 Lemma 10c")
  (statement := /--
  If $c>0$, $g(0,b,c,x)$ decreases with $x$ for $\sqrt{\log x} > -2b/c$. -/)
  (proof := /-- We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a = 0$, it is negative when $u < \frac{-2b}{c}$.
 -/)
  (latexEnv := "lemma")]
theorem lemma_10c {b c : ℝ} (hc : c > 0) :
    StrictAntiOn (g_bound 0 b c) (Set.Ioi (exp ((-2 * b / c) ^ 2))) := sorry

@[blueprint
  "fks2-corollary-11"
  (title := "FKS2 Corollary 11")
  (statement := /--
  If $B \geq 1 + C^2 / 16R$ then $g(1,1-B,C/\sqrt{R},x)$ is decreasing in $x$. -/)
  (proof := /-- This follows from Lemma \ref{fks2-lemma-10a} applied with $a=1$, $b=1-B$ and $c=C/\sqrt{R}$. -/)
  (latexEnv := "corollary")]
theorem corollary_11 {B C R : ℝ} (hB : B ≥ 1 + C ^ 2 / (16 * R)) :
    StrictAnti (g_bound 1 (1 - B) (C / sqrt R)) :=
  sorry

@[blueprint
  "fks2-eq-19"
  (title := "Dawson function, FKS2 (19)")
  (statement := /--
  The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula
  $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$. -/)]
noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)

@[simp] lemma dawson_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ dawson x :=
  mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hx (by simp [Real.exp_nonneg]))

lemma dawson_neg {x : ℝ} : dawson (-x) = - dawson x := by
  calc
    dawson (-x) = exp (-x ^ 2) * ∫ (t : ℝ) in -0..-x, exp (t ^ 2) := by simp [dawson]
    _ = exp (-x ^ 2) * ∫ (t : ℝ) in x..0, exp (t ^ 2) := by
      simp [- neg_zero, ← intervalIntegral.integral_comp_neg]
    _ = _ := by rw [intervalIntegral.integral_symm, dawson]; simp

@[simp] lemma dawson_zero : dawson 0 = 0 := by
  have := dawson_neg (x := 0)
  grind

@[simp] lemma dawson_pos {x : ℝ} (hx : 0 < x) : 0 < dawson x := by
  apply mul_pos (exp_pos _)
  apply intervalIntegral.integral_pos hx (by fun_prop) (by simp [exp_nonneg])
  simp only [Set.mem_Icc, exp_pos, and_true]
  exact ⟨0, by simp [hx.le]⟩

@[simp] lemma dawson_nonpos {x : ℝ} (hx : x ≤ 0) : dawson x ≤ 0 := by
  have := dawson_nonneg (x := -x)
  grind [dawson_neg]

lemma hasDerivAt_dawson {x : ℝ} : HasDerivAt dawson (1 - 2 * x * dawson x) x := by
  have hf₁ : MeasureTheory.StronglyMeasurable (fun x ↦ exp (x ^ 2)) := by measurability
  have hf₂ : Continuous (fun x ↦ exp (x ^ 2)) := by fun_prop
  have : HasDerivAt dawson _ x :=
    (hasDerivAt_pow 2 x).fun_neg.exp.fun_mul (intervalIntegral.integral_hasDerivAt_right
      (hf₂.intervalIntegrable _ _) hf₁.stronglyMeasurableAtFilter (by fun_prop))
  convert this using 1
  rw [dawson, ← exp_add]
  simp
  linear_combination

@[fun_prop]
lemma differentiable_dawson : Differentiable ℝ dawson := fun _ ↦ hasDerivAt_dawson.differentiableAt
@[fun_prop]
lemma continuous_dawson : Continuous dawson := differentiable_dawson.continuous

lemma deriv_dawson_apply {x : ℝ} : deriv dawson x = 1 - 2 * x * dawson x := hasDerivAt_dawson.deriv
lemma deriv_dawson :
  deriv dawson = fun x ↦ 1 - 2 * x * dawson x := funext @deriv_dawson_apply

@[fun_prop] lemma continuous_deriv_dawson : Continuous (deriv dawson) := by
  rw [deriv_dawson]; fun_prop

lemma deriv_deriv_dawson_apply' {x : ℝ} :
    deriv (deriv dawson) x = - 2 * dawson x - 2 * x * deriv dawson x := by
  simp (disch := fun_prop) [deriv_const_mul (2 : ℝ), deriv_dawson]
  ring

lemma deriv_deriv_dawson_apply {x : ℝ} :
    deriv (deriv dawson) x = - 2 * dawson x - 2 * x * (1 - 2 * x * dawson x) := by
  rw [deriv_deriv_dawson_apply']
  simp [deriv_dawson]

lemma dawson_eq_of_deriv_dawson_eq_zero {x : ℝ} (hx : 0 < x) (h : deriv dawson x = 0) :
    dawson x = (2 * x)⁻¹ := by
  simp only [deriv_dawson] at h
  field_simp
  linear_combination -h

/--
Any non-negative local extremum of the dawson function is a local maximum.
-/
lemma dawson_isLocalExtr_isLocalMax {x : ℝ} (hx : 0 ≤ x) (hx : deriv dawson x = 0) :
    IsLocalMax dawson x := by
  apply isLocalMax_of_deriv_deriv_neg _ hx (by fun_prop)
  rw [deriv_deriv_dawson_apply', hx]
  have : x ≠ 0 := by grind [deriv_dawson_apply]
  grind [dawson_pos]

lemma eventuallyEq_of_isMinFilter_of_isMaxFilter {α β : Type*} [PartialOrder β]
    {l : Filter α} {f : α → β} {x : α}
    (h₁ : IsMinFilter f l x) (h₂ : IsMaxFilter f l x) :
    f =ᶠ[l] (fun _ ↦ f x) := by
  filter_upwards [h₁, h₂] using by grind

lemma deriv_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x₀ : ℝ}
    (hf : ContinuousAt f x₀) (h : IsLocalMin f x₀) :
    0 ≤ deriv (deriv f) x₀ := by
  by_contra!
  have := isLocalMax_of_deriv_deriv_neg this h.deriv_eq_zero hf
  have := eventuallyEq_of_isMinFilter_of_isMaxFilter h this
  have : deriv (deriv f) x₀ = 0 := by simpa using this.deriv.deriv_eq
  grind

open Topology in
/-- The Dawson function has no nonnegative local minima. -/
lemma not_dawson_isLocalMin {x : ℝ} (hx : 0 ≤ x) : ¬ IsLocalMin dawson x := by
  intro h
  have hx : deriv dawson x = 0 := h.deriv_eq_zero
  have : x ≠ 0 := by grind [deriv_dawson_apply]
  have : deriv (deriv dawson) x < 0 := by
    rw [deriv_deriv_dawson_apply', hx]
    grind [dawson_pos]
  have := deriv_deriv_nonneg_of_isLocalMin (by fun_prop) h
  grind

/-- Any local maximum of the Dawson function is positive. -/
lemma pos_of_isLocalMax {x : ℝ} (hx : IsLocalMax dawson x) : 0 < x := by
  by_contra!
  apply not_dawson_isLocalMin (x := -x) (by grind)
  have := hx.neg
  rw [← neg_neg (a := x)] at this
  convert this.comp_continuous continuousAt_neg
  ext x
  simp [dawson_neg]

open Topology in
/--
The Dawson function is nowhere locally constant.
That is, it is not constant on any nonempty open set.
-/
lemma not_dawson_eventuallyEq_nhds_const {x c : ℝ} : ¬ dawson =ᶠ[𝓝 x] (fun _ ↦ c) := by
  intro h
  wlog hx : 0 ≤ x
  · refine @this (-x) (-c) ?_ (by grind)
    rw [nhds_neg, ← Filter.map_neg, Filter.eventuallyEq_map]
    filter_upwards [h] with y hy using by grind [dawson_neg]
  exact not_dawson_isLocalMin hx (isLocalMin_const.congr (.symm h))

open Topology in
lemma not_dawson_eventuallyEq_nhdsWithin_const {x c : ℝ} {s : Set ℝ} (hxs : x ∈ closure s)
    (hs : IsOpen s) : ¬ dawson =ᶠ[𝓝[s] x] (fun _ ↦ c) := by
  rw [Filter.EventuallyEq, ← eventually_nhdsWithin_eventually_nhds_iff_of_isOpen hs]
  have : (𝓝[s] x).NeBot := by rwa [← mem_closure_iff_nhdsWithin_neBot]
  intro h
  obtain ⟨x, hx⟩ := h.exists
  exact not_dawson_eventuallyEq_nhds_const hx

section

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [PartialOrder β]

open Topology

/--
If `f` has a local maximum at `x` and attains a minimum on `[x, y]` at `x`,
then `f` is eventually constant equal to `f x` in the right neighborhood of `x`.
-/
lemma eventuallyEq_const_of_isLocalMax_of_isMinOn_left [ClosedIciTopology α]
    {f : α → β} {x y : α} (hxy : x < y)
    (hx : IsLocalMax f x) (hz' : IsMinOn f (Set.Icc x y) x) :
    f =ᶠ[𝓝[≥] x] fun _ ↦ f x := by
  have h₂ : IsMaxFilter f (𝓝[≥] x) x := by
    rw [IsMaxFilter, eventually_nhdsWithin_iff]
    filter_upwards [hx] using by grind
  have h₁ : IsMinFilter f (𝓝[≥] x) x := by
    rw [← nhdsWithin_Icc_eq_nhdsGE hxy]
    filter_upwards [eventually_mem_nhdsWithin] using by grind [isMinOn_iff]
  exact eventuallyEq_of_isMinFilter_of_isMaxFilter h₁ h₂

/--
If `f` has a local maximum at `y` and attains a minimum on `[x, y]` at `y`,
then `f` is eventually constant equal to `f y` in the left neighborhood of `y`.
-/
lemma eventuallyEq_const_of_isLocalMax_of_isMinOn_right [ClosedIicTopology α]
    {f : α → β} {x y : α} (hxy : x < y)
    (hx : IsLocalMax f y) (hz' : IsMinOn f (Set.Icc x y) y) :
    f =ᶠ[𝓝[≤] y] fun _ ↦ f y :=
  eventuallyEq_const_of_isLocalMax_of_isMinOn_left (α := αᵒᵈ) (x := .toDual y) (y := .toDual x)
    hxy hx (by simpa using hz')

end

open Topology in
/--
Given a function `f` continuous on `[x, y]` with local maxima at `x` and `y`, there exists
a point `z` in `(x, y)` which is a local minimum of `f`.
-/
lemma exists_isLocalMin_mem_Ioo {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [LinearOrder α] [DenselyOrdered α] [LinearOrder β] [CompactIccSpace α] [OrderTopology α]
    [OrderClosedTopology β]
    {f : α → β} {x y : α} (hxy : x < y)
    (hf : ContinuousOn f (Set.Icc x y))
    (hx : IsLocalMax f x) (hy : IsLocalMax f y) :
    ∃ z ∈ Set.Ioo x y, IsLocalMin f z := by
  obtain ⟨z, hz, hz'⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hxy.le) hf
  by_cases! h : x = z ∨ y = z
  · obtain ⟨c, t, ht, h⟩ : ∃ c, ∃ t ∈ Set.Ioo x y, f =ᶠ[𝓝 t] (fun _ ↦ c) := by
      by_contra!
      obtain rfl | rfl := h
      · have h := (eventuallyEq_const_of_isLocalMax_of_isMinOn_left hxy hx hz').filter_mono
          (nhdsWithin_mono _ (Set.Ioi_subset_Ici_self))
        rw [Filter.EventuallyEq,
          ← eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Ioi] at h
        have : ∀ᶠ z : α in 𝓝[>] x, False := by
          filter_upwards [h, Ioo_mem_nhdsGT hxy] with z hz hz'
          exact this _ z hz' hz
        rw [Filter.eventually_false_iff_eq_bot] at this
        exact (nhdsGT_neBot_of_exists_gt ⟨y, hxy⟩).ne this
      · have h := (eventuallyEq_const_of_isLocalMax_of_isMinOn_right hxy hy hz').filter_mono
          (nhdsWithin_mono _ (Set.Iio_subset_Iic_self))
        rw [Filter.EventuallyEq,
          ← eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_Iio] at h
        have : ∀ᶠ z : α in 𝓝[<] y, False := by
          filter_upwards [h, Ioo_mem_nhdsLT hxy] with z hz hz'
          exact this _ z hz' hz
        rw [Filter.eventually_false_iff_eq_bot] at this
        exact (nhdsGT_neBot_of_exists_gt (α := αᵒᵈ) ⟨x, hxy⟩).ne this
    exact ⟨_, ht, isLocalMin_const.congr (.symm h)⟩
  · simp only [Set.mem_Icc] at hz
    by_contra! h_contra
    have := hz'.isLocalMin (Icc_mem_nhds (by order) (by order))
    grind

/-- There is at most one local maximum of the Dawson function. -/
lemma unique_isLocalMax {x y : ℝ} (hx : IsLocalMax dawson x) (hy : IsLocalMax dawson y) :
    x = y := by
  have hx0 := pos_of_isLocalMax hx
  have hy0 := pos_of_isLocalMax hy
  wlog hxy : x < y generalizing x y
  · grind
  obtain ⟨z, hz', hz⟩ := exists_isLocalMin_mem_Ioo hxy continuous_dawson.continuousOn hx hy
  cases not_dawson_isLocalMin (by grind) hz

open Topology in
/-- Any local maximum of the Dawson function is a global maximum. -/
lemma isMax_dawson {x : ℝ} (h : IsLocalMax dawson x) : ∀ y, dawson y ≤ dawson x := by
  have hx₀ : 0 < x := pos_of_isLocalMax h
  intro y
  obtain hy | hy : y ≤ 0 ∨ 0 ≤ y := le_total _ _
  · have : dawson y ≤ 0 := dawson_nonpos hy
    have : 0 < dawson x := dawson_pos hx₀
    grind
  by_contra! hc
  have : x ≠ y := by grind
  obtain ⟨z, hz, hz'⟩ : ∃ z ∈ Set.uIcc x y, IsMinOn dawson (Set.uIcc x y) z :=
    isCompact_uIcc.exists_isMinOn Set.nonempty_uIcc continuous_dawson.continuousOn
  have hyz : y ≠ z := by
    rintro rfl
    have := isMinOn_iff.1 hz' x (by simp)
    grind
  obtain hxy | hyx : x < y ∨ y < x := by grind
  · rw [Set.uIcc_of_lt hxy] at hz' hz
    have : x ≠ z := by
      rintro rfl
      have := eventuallyEq_const_of_isLocalMax_of_isMinOn_left hxy h hz'
      exact not_dawson_eventuallyEq_nhdsWithin_const (by simp) isOpen_Ioi
        (this.filter_mono (nhdsWithin_mono _ (Set.Ioi_subset_Ici_self)))
    exact not_dawson_isLocalMin (by grind) (hz'.isLocalMin (by simp; grind))
  · rw [Set.uIcc_of_gt hyx] at hz' hz
    have : x ≠ z := by
      rintro rfl
      have := eventuallyEq_const_of_isLocalMax_of_isMinOn_right hyx h hz'
      exact not_dawson_eventuallyEq_nhdsWithin_const (by simp) isOpen_Iio
        (this.filter_mono (nhdsWithin_mono _ (Set.Iio_subset_Iic_self)))
    exact not_dawson_isLocalMin (by grind) (hz'.isLocalMin (by simp; grind))

/--
Given `0 ≤ y < z` with `x` not between `y,z`, then `dawson y ≠ dawson z`.
-/
lemma dawson_injective_of_nonneg {x y z : ℝ} (h : IsLocalMax dawson x) (hx : x ∉ Set.Icc y z)
    (hy₀ : 0 ≤ y)
    (hyz : y < z) :
    dawson y ≠ dawson z := by
  intro hyz'
  obtain ⟨c, hc', hc⟩ := exists_deriv_eq_zero hyz continuous_dawson.continuousOn hyz'
  have := dawson_isLocalExtr_isLocalMax (by grind) hc
  have := unique_isLocalMax h this
  grind

lemma exists_isLocalMax_of_sign_change {y z : ℝ} (hy0 : 0 ≤ y) (hyz : y < z)
    (hy : 0 ≤ deriv dawson y) (hz : deriv dawson z ≤ 0) :
    ∃ x ∈ Set.Icc y z, IsLocalMax dawson x := by
  obtain ⟨x, hx, hx'⟩ : 0 ∈ deriv dawson '' Set.Icc y z :=
    intermediate_value_Icc' hyz.le (by fun_prop) ⟨hz, hy⟩
  exact ⟨x, hx, dawson_isLocalExtr_isLocalMax (by grind) hx'⟩

lemma strictAntiOn_of_isLocalMax {x y : ℝ} (hx : IsLocalMax dawson x) (hxy : x < y)
    (hy : deriv dawson y < 0) :
    StrictAntiOn dawson (Set.Ici x) := by
  have := pos_of_isLocalMax hx
  have : ∀ y ∈ Set.Ioi x, deriv dawson y < 0 := by
    intro z hz
    by_contra! h
    obtain ⟨t, ht, ht'⟩ : 0 ∈ deriv dawson '' Set.uIcc y z :=
      intermediate_value_uIcc (by fun_prop) (by grind [Set.uIcc_of_le])
    have : Set.uIcc y z ⊆ Set.Ioi x := by grind [Set.mem_uIcc]
    have := dawson_isLocalExtr_isLocalMax (by grind) ht'
    have := unique_isLocalMax hx this
    grind
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (by fun_prop)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro y hy
  grind

lemma strictMonoOn_of_isLocalMax {x y : ℝ} (hx : IsLocalMax dawson x) (hy0 : 0 ≤ y) (hxy : y < x)
    (hy : 0 < deriv dawson y) :
    StrictMonoOn dawson (Set.Icc 0 x) := by
  have := pos_of_isLocalMax hx
  have : ∀ y ∈ Set.Ico 0 x, 0 < deriv dawson y := by
    intro z hz
    by_contra! h
    obtain ⟨t, ht, ht'⟩ : 0 ∈ deriv dawson '' Set.uIcc z y :=
      intermediate_value_uIcc (by fun_prop) (by grind [Set.uIcc_of_le])
    have : Set.uIcc z y ⊆ Set.Ico 0 x := by grind [Set.mem_uIcc]
    have := dawson_isLocalExtr_isLocalMax (by grind) ht'
    have := unique_isLocalMax hx this
    grind
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
  simp only [interior_Icc, Set.mem_Ioo, and_imp]
  grind

@[blueprint
  "fks2-remark-after-corollary-11"
  (title := "FKS2 remark after Corollary 11")
  (statement := /--
  The Dawson function has a single maximum at $x \approx 0.942$, after which the function is
  decreasing. -/)
  (proof := /-- The Dawson function satisfies the differential equation $F'(x) + 2xF(x) = 1$ from which it follows that the second derivative satisfies $F''(x) = −2F(x) − 2x(−2xF(x) + 1)$, so that at every critical point (where we have $F(x) = \frac{1}{2x}$) we have $F''(x) = −\frac{1}{x}$.  It follows that every positive critical value gives a local maximum, hence there is a unique such critical value and the function decreases after it. Numerically one may verify this is near 0.9241 see https://oeis.org/ A133841. -/)
  (latexEnv := "remark")]
theorem remark_after_corollary_11 :
    ∃ x₀ : ℝ, x₀ ∈ Set.Icc 0.924 0.925 ∧ (∀ x, dawson x ≤ dawson x₀) ∧
      StrictAntiOn dawson (Set.Ioi x₀) := sorry

@[blueprint
  "fks2-lemma-12"
  (title := "FKS2 Lemma 12")
  (statement := /--
  Suppose that $E_\theta$ satisfies an admissible classical bound with parameters $A,B,C,R,x_0$.
  Then, for all $x \geq x_0$,
  $$ \int_{x_0}^x |\frac{E_\theta(t)}{\log^2 t} dt| \leq \frac{2A}{R^B} x m(x_0,x)
    \exp(-C \sqrt{\frac{\log x}{R}}) D_+( \sqrt{\log x} - \frac{C}{2\sqrt{R}} )$$
  where
  $$ m(x_0,x) = \max ( (\log x_0)^{(2B-3)/2}, (\log x)^{(2B-3)/2} ). $$
  -/)
  (proof := /-- Since $\varepsilon_{\theta,\mathrm{asymp}}(t)$ provides an admissible bound on $\theta(t)$ for all $t \geq x_0$, we have
\[
\int_{x_0}^{x} \left| \frac{\theta(t) - t}{t(\log(t))^2} \right| dt \leq \int_{x_0}^{x} \frac{\varepsilon_{\theta,\mathrm{asymp}}(t)}{(\log(t))^2} = \frac{A_\theta}{R^B} \int_{x_0}^{x} (\log(t))^{B-2} \exp\left( -C\sqrt{\frac{\log(t)}{R}} \right) dt.
\]
We perform the substitution $u = \sqrt{\log(t)}$ and note that $u^{2B-3} \leq m(x_0, x)$ as defined in (21). Thus the above is bounded above by
\[
\frac{2A_\theta m(x_0, x)}{R^B} \int_{\sqrt{\log(x_0)}}^{\sqrt{\log(x)}} \exp\left( u^2 - \frac{Cu}{\sqrt{R}} \right) du.
\]
Then, by completing the square $u^2 - \frac{Cu}{\sqrt{R}} = \left( u - \frac{C}{2\sqrt{R}} \right)^2 - \frac{C^2}{4R}$ and doing the substitution $v = u - \frac{C}{2\sqrt{R}}$, the above becomes
\[
\frac{2A_\theta m(x_0, x)}{R^B} \exp\left( -\frac{C^2}{4R} \right) \int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv.
\]
Now we have
\begin{align*}
\int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv &\leq \int_{0}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv \\
&= x \exp\left( \frac{C^2}{4R} \right) \exp\left( -C\sqrt{\frac{\log(x)}{R}} \right) D_+\left( \sqrt{\log(x)} - \frac{C}{2\sqrt{R}} \right).
\end{align*}
Combining the above completes the proof. -/)
  (latexEnv := "lemma")]
theorem lemma_12 {A B C R x₀ x : ℝ} (hEθ : Eθ.classicalBound A B C R x₀) (hx : x ≥ x₀) :
  ∫ t in x₀..x, |Eθ t| / log t ^ 2 ≤
    (2 * A) / (R ^ B) * x * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    exp (-C * sqrt (log x / R)) * dawson (sqrt (log x) - C / (2 * sqrt R)) :=
  sorry

noncomputable def ν_asymp (Aψ B C R x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (BKLNW.a₁ (log x₀) * (log x₀) * x₀ ^ (-(1:ℝ)/2) +
      BKLNW.a₂ (log x₀) * (log x₀) * x₀ ^ (-(2:ℝ)/3))

@[blueprint
  "fks2-proposition-13"
  (title := "FKS2 Proposition 13")
  (statement := /--
  Suppose that $A_\psi,B,C,R,x_0$ give an admissible bound for $E_\psi$.  If $B > C^2/8R$, then
  $A_\theta, B, C, R, x_0$ give an admissible bound for $E_\theta$, where
  $$ A_\theta = A_\psi (1 + \nu_{asymp}(x_0))$$
  with
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3}).$$
  -/)]
theorem proposition_13
  (Aψ B C R x₀ : ℝ)
  (h_bound : Eψ.classicalBound Aψ B C R x₀)
  (hB : B > C ^ 2 / (8 * R)) :
  Eθ.classicalBound (Aψ * (1 + ν_asymp Aψ B C R x₀)) B C R x₀ := by sorry

@[blueprint
  "fks2-corollary-14"
  (title := "FKS2 Corollary 14")
  (statement := /--
  We have an admissible bound for $E_\theta$ with $A = 121.0961$, $B=3/2$, $C=2$,
  $R = 5.5666305$, $x_0=2$.
  -/)]
theorem corollary_14 : Eθ.classicalBound 121.0961 (3/2) 2 5.5666305 2 := sorry


@[blueprint
  "fks2-eq-9"
  (title := "mu asymptotic function, FKS2 (9)")
  (statement := /--
  For $x_0,x_1 > 0$, we define
  $$ mu_{asymp}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{2D_+(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}}{\sqrt{\log x_1}}$$.
  -/)]
noncomputable def μ_asymp (A B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
    2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))

@[blueprint
  "fks2-def-5"
  (title := "FKS2 Definition 5")
  (statement := /--
  Let $x_0 > 2$. We say a (step) function $ε_{\diamond,num}(x_0)$ gives an admissible numerical
  bound for $E_\diamond(x)$ if $E_\diamond(x) \leq ε_{\diamond,num}(x_0)$ for all $x \geq x_0$. -/)]
def _root_.Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ (ε x₀)

def _root_.Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

noncomputable def μ_num_1 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    (log x₂) / x₂ * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁)

noncomputable def μ_num_2 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    1 / (log x₁ + log (log x₁) - 1)

noncomputable def μ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ :=
  if x₂ ≤ x₁ * log x₁ then
    μ_num_1 b εθ_num x₀ x₁ x₂.toReal
  else
    μ_num_2 b εθ_num x₀ x₁

noncomputable def επ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ)
    (x₂ : EReal) : ℝ :=
  εθ_num x₁ * (1 + μ_num b εθ_num x₀ x₁ x₂)

noncomputable def default_b (x₀ x₁ : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then log x₀ else log x₁

@[blueprint
  "fks2-remark-7"
  (title := "FKS2 Remark 7")
  (statement := /--
  If
  $$ \frac{d}{dx} \frac{\log x}{x}
    \left( Li(x) - \frac{x}{\log x} - Li(x_1) + \frac{x_1}{\log x_1} \right)|_{x_2} \geq 0 $$
  then $\mu_{num,1}(x_0,x_1,x_2) < \mu_{num,2}(x_0,x_1)$.
  -/)]
theorem remark_7 {x₀ x₁ : ℝ} (x₂ : ℝ) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂)
  (hderiv : deriv (fun x ↦ (log x) / x * (Li x - x / log x - Li x₁ + x₁ / log x₁)) x₂ ≥ 0) :
    μ_num_1 b εθ_num x₀ x₁ x₂ < μ_num_2 b εθ_num x₀ x₁ := by sorry

@[blueprint
  "fks2-remark-15"
  (title := "FKS2 Remark 15")
  (statement := /--
  If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\theta$ with the indicated
  choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
  -/)]
theorem remark_15 (x₀ : ℝ) (h : log x₀ ≥ 1000) :
    Eθ.classicalBound (FKS.A x₀) (3/2) 2 5.5666305 x₀ := by sorry

@[blueprint
  "fks2-theorem-3"
  (title := "FKS2 Theorem 3")
  (statement := /--
  If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound
  with parameters $A,B,C,x_0$ for $E_\theta$, and
  $$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
  then
  $$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x_1) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
  for all $x \geq x_1$.  In other words, we have an admissible bound with parameters
  $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.
  -/)]
theorem theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hE_theta : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
  Eπ.classicalBound (A * (1 + μ_asymp A B C R x₀ x₁)) B C R x₁ :=
  sorry

noncomputable def εθ_from_εψ (εψ : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  εψ x₀ + 1.00000002 * (x₀ ^ (-(1:ℝ)/2) + x₀ ^ (-(2:ℝ)/3) + x₀ ^ (-(4:ℝ)/5)) +
    0.94 * (x₀ ^ (-(3:ℝ)/4) + x₀ ^ (-(5:ℝ)/6) + x₀ ^ (-(9:ℝ)/10))

@[blueprint
  "fks2-proposition-17"
  (title := "FKS2 Proposition 17")
  (statement := /--
  Let $x > x_0 > 2$.  IF $E_\psi(x) \leq \varepsilon_{\psi,num}(x_0)$, then
  $$ - \varepsilon_{\theta,num}(x_0) \leq \frac{\theta(x)-x}{x}
    \leq \varepsilon_{\psi,num}(x_0) \leq \varepsilon_{\theta,num}(x_0)$$
  where
  $$ \varepsilon_{\theta,num}(x_0) = \varepsilon_{\psi,num}(x_0) +
    1.00000002(x_0^{-1/2}+x_0^{-2/3}+x_0^{-4/5}) +
    0.94 (x_0^{-3/4} + x_0^{-5/6} + x_0^{-9/10})$$ -/)]
theorem proposition_17 {x x₀ : ℝ} (hx : x > x₀) (hx₀ : x₀ > 2) (εψ : ℝ → ℝ)
    (hEψ : Eψ x ≤ εψ x₀) :
    -εθ_from_εψ εψ x₀ ≤ (θ x - x) / x ∧ (θ x - x) / x ≤ εψ x₀ ∧
      εψ x₀ ≤ εθ_from_εψ εψ x₀ := by sorry

@[blueprint
  "fks2-lemma-19"
  (title := "FKS2 Lemma 19")
  (statement := /--
  Let $x_1 > x_0 \geq 2$, $N \in \N$, and let $(b_i)_{i=1}^N$ be a finite partition of
  $[x_0,x_1]$.  Then
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
    (Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}).$$ -/)]
theorem lemma_19 {x₀ x₁ : ℝ} (hx₁ : x₁ > x₀) (hx₀ : x₀ ≥ 2)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) :
  |∫ t in x₀..x₁, (θ t - t) / (t * log t ^ 2)| ≤
    ∑ i ∈ Finset.Iio (Fin.last N),
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) :=
  sorry

@[blueprint
  "fks2-lemma-20"]
theorem lemma_20_a : StrictAntiOn (fun x ↦ Li x - x / log x) (Set.Ioi 6.58) := sorry

@[blueprint
  "fks2-lemma-20"
  (title := "FKS2 Lemma 20")
  (statement := /--
  Assume $x \geq 6.58$. Then $Li(x) - \frac{x}{\log x}$ is strictly increasing and
  $Li(x) - \frac{x}{\log x} > \frac{x-6.58}{\log^2 x} > 0$.
  -/)]
theorem lemma_20_b {x : ℝ} (hx : x ≥ 6.58) :
  Li x - x / log x > (x - 6.58) / (log x) ^ 2 ∧
  (x - 6.58) / (log x) ^ 2 > 0 :=
  sorry



@[blueprint
  "fks2-theorem-6"]
theorem theorem_6 {x₀ x₁ : ℝ} (x₂ : EReal) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x.toEReal ≤ x₂) :
  Eπ x ≤ επ_num b εθ_num x₀ x₁ x₂ :=
  sorry

@[blueprint
  "fks2-theorem-6"
  (title := "FKS2 Theorem 6")
  (statement := /--
  Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let
  $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of
  $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that
  $\varepsilon_{\theta,\mathrm{num}}$ gives computable admissible numerical bounds for
  $x = \exp(b_i)$, for each $i=1,\dots,N$.  For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_0) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{\log x_2}{x_2}
    \left( Li(x_2) - \frac{x_2}{\log x_2} - Li(x_1) + \frac{x_1}{\log x_1} \right)$$
  and for $x_2 > x_1 \log x_1$, including the case $x_2 = \infty$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_1) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{1}{\log x_1 + \log\log x_1 - 1}.$$
  Then, for all $x_1 \leq x \leq x_2$ we have
  $$ E_\pi(x) \leq \varepsilon_{\pi,num}(x_1,x_2) :=
    \varepsilon_{\theta,num}(x_1)(1 + \mu_{num}(x_0,x_1,x_2)).$$ -/)]
theorem theorem_6_alt {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) :
  Eπ x ≤ εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) :=
  sorry


@[blueprint
  "fks2-corollary-8"
  (title := "FKS2 Corollary 8")
  (statement := /--
  Let $\{b'_i\}_{i=1}^M$ be a set of finite subdivisions of $[\log(x_1),\infty)$, with
  $b'_1 = \log(x_1)$ and $b'_M = \infty$. Define
  $$ \varepsilon_{\pi, num}(x_1) :=
    \max_{1 \leq i \leq M-1}\varepsilon_{\pi, num}(\exp(b'_i), \exp(b'_{i+1})).$$
  Then $E_\pi(x) \leq \varepsilon_{\pi,num}(x_1)$ for all $x \geq x_1$.
  -/)]
theorem corollary_8 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = log x₁)
    (h_b_end : b' (Fin.last M) = ⊤)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx : x ≥ x₁) :
    Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦
      επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal)
        εθ_num x₁ (exp (b' i.val).toReal)
        (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal)) :=
  sorry

@[blueprint
  "fks2-corollary-21"
  (title := "FKS2 Corollary 21")
  (statement := /--
  Let $B \geq \max(\frac{3}{2}, 1 + \frac{C^2}{16R})$.  Let $x_0, x_1 > 0$ with
  $x_1 \geq \max(x_0, \exp( (1 + \frac{C}{2\sqrt{R}})^2))$. If $E_\psi$ satisfies an admissible
  classical bound with parameters $A_\psi,B,C,R,x_0$, then $E_\pi$ satisfies an admissible
  classical bound with $A_\pi, B, C, R, x_1$, where
  $$ A_\pi = (1 + \nu_{asymp}(x_0)) (1 + \mu_{asymp}(x_0, x_1)) A_\psi$$
  for all $x \geq x_0$, where
  $$ |E_\theta(x)| \leq \varepsilon_{\theta,asymp}(x) :=
    A (1 + \mu_{asymp}(x_0,x)) \exp(-C \sqrt{\frac{\log x}{R}})$$
  where
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3})$$
  and
  $$ \mu_{asymp}(x_0,x_1) = \frac{x_0 \log x_1}{\eps_{\theta,asymp}(x_1)x_1 \log x_0}
    |E_\pi(x_0) - E_\theta(x_0)| + \frac{2 D_+(\sqrt{\log x} - \frac{C}{2\sqrt{R}})}
    {\sqrt{\log x_1}}.$$
  -/)]
theorem corollary_21
  (Aψ B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)))
  (hEψ : Eψ.classicalBound Aψ B C R x₀) :
  let Aθ := Aψ * (1 + ν_asymp Aψ B C R x₀)
  Eπ.classicalBound (Aθ * (1 + (μ_asymp Aθ B C R x₀ x₁))) B C R x₁ :=
  sorry


@[blueprint
  "fks2-corollary-22"
  (title := "FKS2 Corollary 22")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 9.2211 x \sqrt{\log x} \exp(-0.8476 \sqrt{\log x})
  \]
  for all $x \geq 2$.
  -/)]
theorem corollary_22 : Eπ.classicalBound 9.2211 1.5 0.8476 1 2 := sorry

def table6 : List (List ℝ) := [[0.000120, 0.25, 1.00, 22.955],
                                 [0.826, 0.25, 1.00, 1.000],
                                 [1.41, 0.50, 1.50, 2.000],
                                 [1.76, 1.00, 1.50, 3.000],
                                 [2.22, 1.50, 1.50, 3.000],
                                 [12.4, 1.50, 1.90, 1.000],
                                 [38.8, 1.50, 1.95, 1.000],
                                 [121.107, 1.50, 2.00, 1.000],
                                 [6.60, 2.00, 2.00, 3.000]]

@[blueprint
  "fks2-corollary-23"
  (title := "FKS2 Corollary 23")
  (statement := /--
  $A_\pi, B, C, x_0$ as in Table 6 give an admissible asymptotic bound for $E_\pi$ with
  $R = 5.5666305$.
  -/)]
theorem corollary_23 (Aπ B C x₀ : ℝ) (h : [Aπ, B, C, x₀] ∈ table6) :
    Eπ.classicalBound Aπ B C 5.5666305 x₀ := sorry

noncomputable def table7 : List ((ℝ → ℝ) × Set ℝ) :=
  [ (fun x ↦ 2 * log x * x^(-(1:ℝ)/2), Set.Icc 1 57),
    (fun x ↦ (log x)^(3/2) * x^(-(1:ℝ)/2), Set.Icc 1 65.65),
    (fun x ↦ 8 * π * (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 8 60.8),
    (fun x ↦ (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 1 70.6),
    (fun x ↦ (log x)^3 * x^(-(1:ℝ)/2), Set.Icc 1 80),
    (fun x ↦ x^(-(1:ℝ)/3), Set.Icc 1 80.55),
    (fun x ↦ x^(-(1:ℝ)/4), Set.Icc 1 107.6),
    (fun x ↦ x^(-(1:ℝ)/5), Set.Icc 1 134.8),
    (fun x ↦ x^(-(1:ℝ)/10), Set.Icc 1 270.8),
    (fun x ↦ x^(-(1:ℝ)/50), Set.Icc 1 1358.6),
    (fun x ↦ x^(-(1:ℝ)/100), Set.Icc 1 3757.6)
  ]

@[blueprint
  "fks2-corollary-24"
  (title := "FKS2 Corollary 24")
  (statement := /--
  We have the bounds $E_\pi(x) \leq B(x)$, where
  $B(x)$ is given by Table 7.
  -/)]
theorem corollary_24 (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, log x ∈ I → Eπ x ≤ B x := sorry

@[blueprint
  "fks2-corollary-26"
  (title := "FKS2 Corollary 26")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 0.4298 \frac{x}{\log x}
  \]
  for all $x \geq 2$.
  -/)]
theorem corollary_26 : Eπ.bound 0.4298 2 := sorry

end FKS2
