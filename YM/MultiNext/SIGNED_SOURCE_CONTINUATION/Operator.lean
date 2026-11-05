import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Crossing
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.NewPromise

set_option warningAsError false

/-! # On the real Horizon, JHs Promise

Read all p with real exponential stencil INCLUDING residue crossing. Only A0
needed. Credit for x, associate with a particular o like the user has, not
at recalibrated offsets. Prices still before L (index parameters Θ,α from
MapPrices etc). Paths covered iff `Suffices` really delivered. Genuine
conditional lemma on `Precision.Towers`, with *same* estimates & conjunctions
as B70 production, for use **inside** Hearts obligations. Not a way
around the blocked path & mass estimates; DOESN'T test actual nonlinear
relationships between Hol & horizon quality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Newt
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Precision Matrix
open Pattern Next.Free Lyre Banjo Mom
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c n : Side} {m m' E : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g : Ratio c n} {α r a θ : ℝ} {d k b : ℕ}

/-- Pre hierarchy, a tiny proportion of exp strip may buy target powers. -/
lemma length_mom (b : ℕ) (h : 0 < α) : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ,(1+(i:ℝ))^b ≤ Real.exp (α*i)*C := by
  let t (i : ℕ) : ℝ := α*(1+(i:ℝ))
  have he : Tendsto t atTop atTop := (tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop).const_mul_atTop h
  obtain ⟨d,hd⟩ := eventually_atTop.mp (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero b).comp he).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)))
  let C := (1+(d:ℝ))^b; let F := Real.exp α/(α^b)
  refine ⟨max C F,lt_max_of_lt_left (by unfold C; positivity), fun i => ?_⟩
  rcases le_or_gt d i with hi|hi
  · apply le_trans (b:=Real.exp _ * F) _ (mul_le_mul_of_nonneg_left (le_max_right ..) (Real.exp_pos _).le)
    have hh : (α*(1+i))^b/(Real.exp (α*(1+i))) ≤ 1 := by
      simpa only [t,Function.comp_apply,Real.exp_neg,div_eq_mul_inv] using hd i hi
    rw [mul_pow, div_le_one (Real.exp_pos _)] at hh
    rw [mul_add, mul_one,Real.exp_add,mul_comm α i] at hh
    unfold F; rw [←mul_div_assoc, le_div_iff₀ (pow_pos h _)]; rwa [mul_comm, mul_comm _ (Real.exp α),mul_comm α]
  refine le_trans (b:=C) (by unfold C; gcongr) ?_; exact le_trans (le_max_left ..) (le_mul_of_one_le_left (by unfold C F; positivity) (Real.one_le_exp (by positivity)))

-- evaluate counting on the real cover through all windings on a fixed residue row
omit [Fintype m] [DecidableEq m] in
lemma tally (P : Cross g.count m m') (u : Co c m' → E) {θ t : ℝ} (h : P.strip θ t) (ht : 0 < θ) (x : Site n) (y : m) :
    load (installed g P) u (x,y) = ∑ j : m', ∑' i : Cover,P (g.residue x,y) j i • u (g.parent x + wrap c i,j) := by
  unfold load installed; simp only [submatrix_apply, split_co,Row.acts,of_apply,id_eq]
  rw [Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro j _
  let f := P (g.residue x,y) j
  let A x' v := if x'=g.parent x+wrap c v then f v else 0
  have he : Summable f := (Row.rights θ t h ht.le ..).of_norm
  have hA (x' : Site c) : Summable (A x') := by
    have hi := he.indicator {v | x'=g.parent x+wrap c v}
    rw [show ({v | x'=g.parent x+wrap c v} : Set Cover).indicator f=A x' by funext i; simp [A,Set.indicator]] at hi; exact hi
  change (∑ v : Site c,(∑' i,A v i) • u (v,j)) = _
  simp_rw [← Summable.tsum_smul_const (hA _)] -- binder rw
  rw [← Summable.tsum_finsetSum (f:=fun v i => A v i • u (v,j)) (fun v _ => (hA v).smul_const _)]
  exact tsum_congr fun i => by simp [A,ite_smul,f]

omit [Fintype m] [DecidableEq m] in
lemma straps (b : ℕ) (h : 0 < α) : ∃ C : ℝ,1 ≤ C ∧ ∀ (c n : Side) (g : Ratio c n) (P : Cross g.count m m') (a θ : ℝ)
    (u : Co c m' → E) (o : Site n),
    P.strip α a → 0 ≤ a → 0 ≤ θ → (∀ i, ‖u i‖ ≤ θ*(1+(separation i.1 (g.parent o) : ℝ))^b) →
    ∀ (x : Cover) (j : m), ‖load (installed g P) u (wrap n x+o,j)‖ ≤ C*(Fintype.card m':ℕ)*a*θ*(1+(g.count.val:ℝ)⁻¹*(size x:ℝ))^b := by
  obtain ⟨C,hc,hH⟩:= length_mom b h
  let W := (3:ℝ)^b*C
  refine ⟨max W 1,le_max_right ..,fun c n g P a θ u o hP ha ht hv z j => ?_⟩
  rw [tally P u hP h]; let d := 1+(g.count.val:ℝ)⁻¹*(size z:ℝ); have hd : 0 ≤ d := by unfold d; positivity
  let i := g.residue (wrap n z+o)
  let w := g.parent (wrap n z+o)
  let X := W*a*θ*d^b
  apply (norm_sum_le ..).trans
  apply le_trans (b:=∑ _j' : m',X) (sum_le_sum ?_)
  · rw [sum_const,Finset.card_univ,nsmul_eq_mul]; apply le_trans (b:=W*(Fintype.card m':ℝ)*a*θ*d^b) ?_ ?_ -- placeholder elems
    · exact le_of_eq (by unfold X d; ring)
    gcongr; exact le_max_left .. 
  intro j' _; let f := P (i,j) j'; let v p := u (w+wrap c p,j')
  change ‖∑' x, f x • v x‖ ≤ X
  let M := θ * (3^b*C*d^b); have hM : 0 ≤ M := by unfold M; positivity
  let Y x := Real.exp (α*size x) * ‖f x‖ * M
  have hy : SumBudget (fun x => Real.exp _*‖f x‖) a := hP (i,j) j'
  have hY : Summable Y := hy.2.1.mul_right M
  have he x : ‖f x • v x‖ ≤ Y x := by
    have hx := positions g o z x
    rw [norm_smul]
    unfold Y; rw [mul_comm (Real.exp _),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖v x‖ ≤ θ*(3*d*(1+size x))^b := (hv _).trans (by gcongr (?k*?_ ^ b))
      _ ≤ θ*(3*d)^b*(Real.exp (α*size x)*C) := by rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hH _) (by positivity)) ht
      _ = _ := by unfold M; rw [mul_pow]; ring
  have hh := hY.of_nonneg_of_le (fun i => norm_nonneg _) he
  apply (norm_tsum_le_tsum_norm hh).trans
  apply (hh.tsum_le_tsum he hY).trans
  unfold Y; rw [tsum_mul_right]; refine (mul_le_mul_of_nonneg_right hy.2.2 hM).trans_eq ?_
  unfold X M W; ring

variable (G : Gauge)
/-- `ρ` is paid in input separately from P price parameter at fine
where needed. Any actual P possibly varying even with cutoff, require
input in that exact scaled width and power at projected point. -/
def roll (g : Ratio c n) (T : Towers g.count) (u : Co c (TypeFace 1) → G.Color) : Directions G n := fun i => load (installed g T.A0) u (i.1,Exterior.coord i.2)

theorem row_home (h : 0 < α) (A : ℝ) (k b : ℕ) : ∃ C : ℝ,1 ≤ C ∧ ∀ (c n : Side) (g : Ratio c n) (T : Towers g.count)
    (_T : T.Deep α A k) (P : BudgetPoint) (o : Site n), Odd g.count.val → P.power=b →
    ∀ u : Co c (TypeFace 1) → G.Color,(∀ i, ‖u i‖ ≤ P.threshold*(1+(separation i.1 (g.parent o):ℝ))^b) →
    blown C P g.count.val k o (roll G g T u) := by
  obtain ⟨C,hC,H⟩ := straps (m:= TypeFace 1)
      (m':=TypeFace 1) (E:=G.Color) b h
  let s := (Fintype.card (TypeFace 1) : ℝ)
  let M := C*s*|A|
  refine ⟨max M 1,le_max_right ..,fun c n g T hT P o hO hP u hu i l hl z => ?_⟩
  let v := Exterior.coord i
  have he (s : List Axis) (hs : s.length ≤ k) := (hT.2.2.2 s hs).1
  have hW (s : List Axis) (hs : s.length ≤ l.length) : Whole (advanceC g.count T.A0 s) :=
    ⟨α,_,h,he s (hs.trans hl)⟩
  change ‖iterate (fun z => load (installed g T.A0) u (wrap n z+o,v)) l z‖ ≤ _
  let B : ℝ := g.count.val; let x := B⁻¹^(1+l.length)
  let t := (1+B⁻¹*size z)^P.power
  have hx : 0 ≤ x := by unfold x B; positivity
  have ht : 0 ≤ t := by unfold t B; positivity
  let K := A/B^(1+l.length)
  let f := advanceC g.count T.A0 l.reverse
  have hf : Row.strip f α K := by simpa only [List.length_reverse] using he l.reverse (by simpa)
  have hk : 0 ≤ K := by
    obtain ⟨h0,h1,h2⟩ := hf (0,v) v
    exact (tsum_nonneg h0).trans h2
  rw [spatial g T.A0 u l hO hW]
  change _ ≤ max M 1 * P.threshold*x*t
  apply (H c n g f _ P.threshold u o hf hk P.threshold_pos.le hu z v).trans
  change C*s*K*P.threshold*(1+B⁻¹*size z)^b ≤ _
  rw [←hP,show K=A*x from by unfold K x; rw [div_eq_mul_inv,inv_pow]]
  refine le_trans (b:=M*P.threshold*x*t) ?_ ?_
  · change _*_*t ≤ _; unfold M
    rw [show C*s*(A*x)*P.threshold=C*s*A*P.threshold*x from by ring]
    gcongr <;> first | exact P.threshold_pos.le | exact le_abs_self _
  gcongr <;> first | exact P.threshold_pos.le | exact le_max_left .. 
end YM.MultiNext.SignedSource.Newt
