import YM.Next.FREE_KERNELS.Cable
import YM.Next.FREE_KERNELS.Ends

/-!
# Cube estimates for residue columns

Uses true fine differences (including change in coarse base); strength for
order v uses the J-v product weight. Pay in scaled analytic cube still
before L. We leave L scales explicit even in symbols on the cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate
variable {ι α β : Type*} {j t : ℕ}

abbrev Thread (j t : ℕ) (α β : Type*) := ∀ P : Flight j t, Momentum → Site P.L → Matrix α β ℂ

/-- Budget verified uniformly in `Flight`s. Storing the *rescaled*
alias blocks here, even at zero. The laws are on the full enlarged real
cube and allow reciprocal shifts on overlap cubes. -/
structure Secured (f : Thread j t α β) : Prop where
  /-- Sigma gives joint constants including any particular alias index. -/
  pay : Pay (fun x : Σ P : Flight j t, Site P.L => decay j x.2) fun i p => f i.1 p i.2
  relay (P : Flight j t) (p : Momentum) (hp : p∈realCube zone) (x : Cover)
      (hx : p+reciprocal x∈realCube zone) (l : Site P.L) : f P (p+reciprocal x) l=f P p (l+wrap P.L x)
  pearl (P : Flight j t) (p : Momentum) (hp : p∈realCube zone) (l : Site P.L) : shade (f P p l)=f P (-p) (-l)

lemma secure_both (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4 ≤ t) :
    Secured (Flight.pilot (j:=j) (t:=t) k) ∧ Secured (Flight.wire (j:=j) (t:=t) k) := by
  refine ⟨⟨?_,fun P p h x hx l => ?_,fun P p h l => ?_⟩,⟨?_,fun P p h x hx l => ?_,fun P p h l => ?_⟩⟩
  · exact Flight.pilot_cost k hk hj ht (fun i : Σ P : Flight j t, Site P.L => i.1) (fun i => i.2)
  · exact (P.knots_shift k hk h x hx l).1
  · exact (P.knots_reflect k hk h l).1
  · exact Flight.wire_budget k hk hj ht (fun i : Σ P : Flight j t, Site P.L => i.1) (fun i => i.2)
  · exact (P.knots_shift k hk h x hx l).2
  · exact (P.knots_reflect k hk h l).2

def toll (L : Side) (v : ℕ) := ((L.val:ℂ)^v)⁻¹

def listChip (p : Momentum) (u : List Axis) := (u.map (fun i => chip (p i))).prod

def spread (f : Thread j t α β) (e : ℕ) (u : List Axis) (P : Flight j t) (r : Site P.L) (p : Momentum) := ∑ i : Site P.L,
      mode (aliasAt p i) (lift r) • ((toll P.L e*listChip (aliasAt p i) u) • f P p i)

def meshBook (f : Thread j t α β) (e : ℕ) (u : List Axis) (P : Flight j t) : Cross P.L α β := fun i k =>
      record (spread f e u P i.1) i.2 k

lemma differential_bound (F : ι → Flight j t) (l : ∀ i, Site (F i).L) (e : ℕ) (u : List Axis) :
    Moderate (fun i => ((((F i).L.val:ℝ)^(e+u.length))⁻¹*grade (l i)^u.length)) fun i p =>
      toll (F i).L e*listChip (aliasAt p (l i)) u := by
  induction u generalizing e with
  | nil =>
    simp only [List.length_nil,Nat.add_zero,pow_zero,mul_one,listChip,List.map_nil,List.prod_nil]
    apply Moderate.bounded_const _ 1 one_pos; intro i; unfold toll; rw [norm_inv,norm_pow,Complex.norm_natCast]; simp
  | cons a u ih =>
    have hh := (ih (e+1)).mul (Flight.sigQ_budget F l fun _ => a)
    have he (L : Side) (p : Momentum) : toll L e*listChip p (a::u)=(toll L (e+1)*listChip p u)*tripQ L p a := by
      have he := side_ne L; unfold toll listChip tripQ
      simp only [List.map_cons,List.prod_cons, pow_succ]; field_simp
    simp_rw [he]
    apply hh.raise_price
    intro i
    simp only [List.length_cons, pow_succ,show e+(u.length+1)=e+1+u.length by omega]; rw [mul_assoc]

lemma residue_cost (F : ι → Flight j t) (l r : ∀ i, Site (F i).L) :
    Moderate (fun _ : ι => 1) fun i p => mode (aliasAt p (l i)) (lift (r i)) := by
  refine ⟨zone, Real.exp (4*zone),zone_pos, Real.exp_pos _,fun i => ⟨fun p hp => ?_,fun p hp => ?_⟩⟩
  · unfold mode aliasAt; fun_prop
  let n : Side := (F i).L
  have hm := reward (aliasAt p (l i)) (lift (r i)) (zone/n.val)
    (fun x => ((alias_in_cube_precise hp (l i) (F i).odd).1 x).le)
  rw [mul_one]; apply hm.trans; apply Real.exp_le_exp.mpr
  have he : size (lift (r i)) ≤ 4*n.val := by
    unfold size
    have hh (x : Axis) : (lift (r i) x).natAbs≤n.val := by obtain hh := lift_centers (r i) x; unfold n; omega
    exact (Finset.sum_le_sum fun i _ => hh i).trans (le_of_eq (by simp [Axis]))
  rw [mul_comm,← mul_div_assoc,div_le_iff₀ (side_pos _)]
  have hh : (size (lift (r i)):ℝ) ≤ 4*n.val := by exact_mod_cast he
  nlinarith [zone_pos]

namespace Secured
variable {f : Thread j t α β}
lemma propels (h : Secured f) (hj : 4≤j) (e : ℕ) {u : List Axis} (hu : u.length≤j-2)
    (F : ι → Flight j t) (r : ∀ i, Site (F i).L) :
    Pay (fun i => ((((F i).L.val:ℝ)^(e+u.length))⁻¹)) fun i => spread f e u (F i) (r i) := by
  refine ⟨fun i => by positivity, fun a b => ?_⟩
  simp only [spread,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  let L (i : ι) := (F i).L
  let y (i : ι) := (((L i).val:ℝ)^(e+u.length))⁻¹
  let s (i) := (Finset.univ : Finset (Site (L i)))
  obtain ⟨C,hC,hT⟩ := decay_cost
  apply Moderate.sum_family s (fun i l => y i*decay 2 l) ⟨C,hC,fun i => (by
    rw [← Finset.mul_sum,mul_comm C]; exact mul_le_mul_of_nonneg_left (hT (L i)) (by unfold y; positivity))⟩
  let I := Σ i, {l // l∈s i}
  let m (i : I) := F i.1
  let q (i : I) := i.2.val
  have he := differential_bound m q e u
  have hp := residue_cost m q (fun i => r i.1)
  have hc := (h.pay.tap a b).index (fun i => ⟨m i,q i⟩)
  apply (hp.mul (he.mul hc)).raise_price
  intro i
  have hn : u.length+2≤j := by omega
  dsimp only
  rw [one_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (mul_le_mul_of_nonneg_left (decay_anti _ (show 2+u.length≤j by omega)) (pow_nonneg (grade_pos _).le _)).trans (absorbs ..)

lemma list_repeat (p : Momentum) (x : Cover) (u : List Axis) : listChip (p+reciprocal x) u=listChip p u := by
  unfold listChip; simp only [Pi.add_apply,reciprocal,chip_repeat]
lemma list_bar {p : Momentum} (hp : physical p) (u : List Axis) : star (listChip p u)=listChip (-p) u := by
  induction u with
  | nil => simp [listChip]
  | cons a u ih =>
    unfold listChip at *; simp only [List.map_cons,List.prod_cons,star_mul,ih,flip_chip,Pi.neg_apply]; rw [show star (p a)=p a from congr_fun hp a]; ring
lemma layout (h : Secured f) (e : ℕ) (u : List Axis) (P : Flight j t) (r : Site P.L) {p : Momentum}
    (hp : p∈realCube zone) (x : Cover) (hx : p+reciprocal x∈realCube zone) :
    spread f e u P r (p+reciprocal x)=spread f e u P r p := by
  unfold spread
  rw [← Equiv.sum_comp (Equiv.addRight (wrap P.L x)) (fun i => mode (aliasAt p i) (lift r) • ((toll P.L e*listChip (aliasAt p i) u) • f P p i))]
  apply Finset.sum_congr rfl; intro i _
  obtain ⟨y,he⟩ := alias_exchange p i x
  rw [h.relay P p hp x hx i,he,list_repeat]; simp only [mode_phase,mode_periodic,mul_one]; rfl
lemma palette (h : Secured f) (e : ℕ) (u : List Axis) (P : Flight j t) (r : Site P.L) {p : Momentum}
    (hp : p∈realCube zone) : (spread f e u P r (-p)).map star=spread f e u P r p := by
  have he (p : Momentum) (hp : p∈realCube zone) : shade (spread f e u P r p)=spread f e u P r (-p) := by
    have hg (q : Momentum) (hq : physical q) (x : Cover) : star (mode q x)=mode (-q) x := by
      have he := mode_adjoint q x; rw [show star q=q from hq,mode_opposite,← mode_inverse] at he; exact he
    unfold spread
    have hy (f : Site P.L → Matrix α β ℂ) : shade (∑ i, f i)=∑ i, shade (f i) := by ext a b; simp [shade,Matrix.sum_apply]
    rw [hy,← Equiv.sum_comp (Equiv.neg (Site P.L)) (fun i => mode (aliasAt (-p) i) (lift r) • ((toll P.L e*listChip (aliasAt (-p) i) u) • f P (-p) i))];
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm := alias_real hp.1 (i:Site P.L)
    have hz : star (toll P.L e)=toll P.L e := by simp [toll]
    rw [shade_weight,shade_weight,hg _ hm,star_mul,h.pearl P p hp,list_bar hm,hz];
    simp only [Equiv.neg_apply,alias_reverse _ P.odd]; rw [mul_comm]
  simpa only [shade,neg_neg] using he (-p) (realCube_neg hp)
end Secured
end YM.Next.Free
