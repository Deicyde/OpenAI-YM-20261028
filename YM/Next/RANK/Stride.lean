import YM.Bid.Loan
import YM.Next.RANK.Bird
import YM.Next.RANK.Lens

/-!
# Literal leg test reconciliation

Order compared against real derivative of the *Maxwell curl* at the aligned coordinates. Includes
y chain sign. Weight lower terms from exact stencil Taylor sample cost small.
No Fourier comparison claimed merely from definitions about Sigma matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Prayer
open Function Set Lattice Wilson RG Maxwell Maxwell.Wick Labels Normal Beamer Perch Configuration   Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {d n : ℕ} {x : Points n}
variable (i : KeyIn G d)

-- coefficients on the actual shell

def scans (i : Key G) : Maxwell.Probe G i.1 := ((axes G i.1).coord i.2).comp (Maxwell.gaugeJet (G:=G))
lemma probeders (i : Key G) : scans i = ∑ j, scans i (frame G i.1 j) • coordinateLeg (⟨i.1,j⟩ : Slot G) := by
  ext1 v; conv_lhs => rw [← (Maxwell.frame G _).sum_repr v]
  rw [map_sum,LinearMap.sum_apply (M:=Shell G i.1) (σ₁₂:=RingHom.id ℝ)]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun _ _ => mul_comm ..

private lemma linear_c {G : Gauge} (Q : Normal.Symmetric (Fin n × Slot G)) (i j) (H : Slot G →₀ ℂ) (f : Slot G →₀ ℂ) :
    treats Q (Finsupp.mapDomain (fun x => (i,x)) H) (Finsupp.mapDomain (fun x => (j,x)) f) =
    Finsupp.linearCombination ℂ (fun x => Finsupp.linearCombination ℂ (fun p => Q.cov (i,p) (j,x)) H) f := by
  unfold treats; rw [Finsupp.linearCombination_mapDomain,Finsupp.linearCombination_mapDomain]
  apply congr_arg (fun n => Finsupp.linearCombination ℂ n f); funext x
  simp only [Function.comp_apply,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply]

lemma pays {x : Points n} (hx : x∈conf n) (i j : Fin n) (he : i≠j) (s : KeyIn G d) (t : KeyIn G d) :
    (currentX hx G d).cov (i,s) (j,t)= ((Maxwell.legKernel (scans s.val) (scans t.val) (x i-x j) : ℝ) : ℂ) := by
  unfold currentX Normal.scope perSlot; dsimp only; rw [linear_c]
  let J := Maxwell.pairing (show x i - x j∈Maxwell.away from sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne he)) (G:=G) (j:=s.val.1) (l:=t.val.1)
  change _= ((J (scans _) (scans _) : ℝ) : ℂ)
  conv_rhs => rw [probeders s.val, show (scans t.val)=(∑ j, scans t.val (Maxwell.frame G t.val.1 j) • coordinateLeg (⟨t.val.1,j⟩ : Slot G)) from probeders t.val]

  rw [map_sum (J)]; simp only [LinearMap.sum_apply,map_smul]
  simp only [mapper,map_sum,map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro z _; simp only [Finsupp.linearCombination_single,one_smul]; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  unfold frameX; dsimp only; rw [if_neg he]; rfl
lemma dies {x : Points n} (hx : x∈conf n) (i : Fin n) (s : KeyIn G d) (t : KeyIn G d) : (currentX hx G d).cov (i,s) (i,t)=0 := by
  unfold currentX Normal.scope perSlot; dsimp only; rw [linear_c]; simp [frameX, Finsupp.linearCombination_apply]

-- fixed order normalized identity. probe test at physical (color basis) from coefficient.

def Sharp (L : Degree G) (v : Taylor G L.degree) : ℝ := gesture L (sweep L.degree v)
lemma photos (L : Degree G) : Maxwell.constrain (G:=G) (fromF G (basis ∘ L.layout) L.paint L.a.val.1 L.a.val.2) =
    ∑ j, ((L.degree.factorial:ℝ)⁻¹ * Sharp L (axes G L.degree j)) • scans (G:=G) ⟨L.degree,j⟩ := by
  ext1 p
  let P:= gaugeJet p
  have H (y : Axis) (z : Axis) : p.val y z = takeCurl P y z := by rw [show takeCurl P = p.val from match_leg _]
  change p.val L.a.val.1 L.a.val.2 _ _ = _
  rw [H]
  have hf : Sharp L P = (L.degree.factorial:ℝ) * (takeCurl P L.a.val.1 L.a.val.2) (basis ∘ L.layout) L.paint := by
    unfold Sharp; rw [gesture_hits, show sweep L.degree P=inspect P from rfl, Beamer.inspected,CellsInt.test_top]; rfl
  apply mul_left_cancel₀ (show (L.degree.factorial:ℝ) ≠ 0 by positivity)
  rw [← hf,LinearMap.sum_apply (M:=Shell G L.degree) (σ₁₂:=RingHom.id ℝ),Finset.mul_sum]
  unfold Sharp; conv_lhs => rw [← (axes G _).sum_repr P,map_sum,map_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [map_smul, map_smul, LinearMap.smul_apply]; change (_:ℝ)*_= _*(_ * ((axes G L.degree).repr P j))
  field_simp

-- derivative spec in terms of symmetric Tensor.coeff; convert to true derivative values

def light (L K : Degree G) (x y : E4) : ℝ :=
  (L.degree.factorial * (K.degree.factorial:ℝ)) *
    if L.paint = K.paint then Tensor.coeff (fun y => Tensor.coeff (fun x => bareCurl L.a.val.1 L.a.val.2 K.a.val.1 K.a.val.2 (x-y)) L.degree x (basis ∘ L.layout)) K.degree y (basis ∘ K.layout)
    else 0

lemma measured {x : Points n} (hx : x ∈ conf n) {i j : Fin n} (he : i≠j) (u v : Hub G d 0) :
    (∑ s : Fin (Labels.dim G u.val.degree),
      ∑ t : Fin (Labels.dim G v.val.degree),
        let p := (fan (a:=0) s u.property.2.2 u.property.2.1).val
        let q := (fan (a:=0) t v.property.2.2 v.property.2.1).val
        ((currentX hx G d).cov (i,p) (j,q)).re * (gesture u.val (tester p.val)*gesture v.val (tester q.val))) = light u.val v.val (x i) (x j) := by
  simp_rw [pays hx i j he]; let a:=u.val; let b:=v.val
  let y:= x i;let z:=x j; let s:= y-z; have ht : y≠z := (show Injective x.ofLp from hx).ne he
  let P := Maxwell.pairing (show s∈away from sub_ne_zero.mpr ht) (G:=G) (j:=a.degree) (l:=b.degree)
  unfold light; rw [← Maxwell.reads_mixed _ _ _ _ _ _ _ _ ht]
  change _=(a.degree.factorial*(b.degree.factorial:ℝ))*P (constrain _) (constrain _)
  rw [photos a,photos b, map_sum P,LinearMap.sum_apply,Finset.mul_sum]
  -- factors
  apply Finset.sum_congr rfl; intro p _; rw [map_sum (P _),Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _; rw [map_smul P,LinearMap.smul_apply,_root_.map_smul]
  set c := ((a.degree.factorial:ℕ) : ℝ)
  set d' := (↑(b.degree.factorial):ℝ)
  change (P (scans ⟨a.degree,p⟩) (scans ⟨b.degree,q⟩)) * (Sharp a (axes G a.degree p)*Sharp b (axes G b.degree q))=
      (c*d')*((c⁻¹*_) • ((d'⁻¹*_) • P (scans ⟨a.degree,p⟩) (scans ⟨b.degree,q⟩)))
  dsimp only [smul_eq_mul]
  have hp : c>0 := by unfold c; positivity
  have he' : d'>0 := by unfold d'; positivity
  field_simp
end YM.Next.Rank.Prayer
