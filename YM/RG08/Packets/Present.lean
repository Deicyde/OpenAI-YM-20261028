import YM.RG08.Packets.FlatStep

/-!
# Using Beds as translation-invariant analytic curvature packets
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG Precision
open scoped Topology ENNReal

set_option autoImplicit false
variable {α : Type} [Fintype α] {c f : Side}
    {Y H : Bed} {p q σ : ℝ} {R S : Row α α}

def saddle (R : Row α α) : Packet 1 α := fun x y=> plain R x (y 0)

theorem settled (h : R.strip σ p) : Folded σ (saddle R) (Fintype.card α * p) := by
  intro x
  rw [← (identify (Market α)).symm.tsum_eq]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card α :ℝ)),ENNReal.ofReal_natCast]
  apply convert_market
  intro i
  have he := (plain0 h (le_refl _)).1 x i
  simpa [saddle,identify,expense,delta,sep_comm] using he -- simp sep_comm expensive?

 omit [Fintype α] in
theorem display_sub {A : Kernel α α} {B : Kernel α α} (x : Market α) (y : Co c α)
    (hA : Summable (A x))(hB:Summable (B x)) :
    display (fun x y=>A x y-B x y) c x y = display A c x y - display B c x y := by
  let s := {z:Cover | wrap c z=y.1}
  classical
  have h {T : Kernel α α} (hT : Summable (T x)) : Summable fun z=> if wrap c z = y.1 then T x (z,y.2) else 0 := by
    have H : Summable fun z : Cover=> T x (z,y.2) := by
      apply hT.comp_injective (i:=fun z=> (z,y.2))
      intro a b h; exact congr_arg Prod.fst h
    exact (H.indicator s).congr fun z=>Set.indicator_apply ..
  rw [display,display,display,← Summable.tsum_sub (h hA) (h hB)]
  refine tsum_congr fun _=> ?_; split <;> simp

def roadSum (R : Row α α) (a b : α) := ∑'z,R a b z

 omit [Fintype α] in
theorem roadSum_price (R : Row α α) (a b : α) : Complex.ofReal (roadSum R a b)=R.read 0 a b := by
  rw [roadSum,Row.read,Matrix.of_apply,Laurent.read]; simp [← Complex.ofReal_tsum]

omit [Fintype α] in
theorem saddle_sum {R : Row α α} (x : Market α) (i : α) :
    (∑' z,saddle R x fun _=> (z,i))=roadSum R x.2 i := by
  rw [← (Equiv.addRight x.1).tsum_eq]
  refine tsum_congr fun z=>?_ ; unfold saddle plain; rw [show ((Equiv.addRight x.1) z)=z+x.1 from rfl]; simp

theorem turn_class {b b': Clip} {e D e' D' : ℝ} (hY : Floor Y b c e D) (hH : Floor H b' c e' D')
    (hp : Y.metric.strip σ p) (hq : H.metric.strip σ q) (hσ : 0 ≤ σ)(he : 0 ≤ p)(he' : 0 ≤ q):
    let B : Packet 1 Faces := fun x y=> saddle Y.metric x y - saddle H.metric x y
    neutral B ∧ town 1 B ∧ Folded σ B (Fintype.card Faces*(p+q)) ∧ Sigil B c (quadratic Y c-quadratic H c) := by
  intro B
  have hy := settled hp
  have hh := settled hq
  refine ⟨?_,fun x y u=>?_,?_,Y.metric.acts c-H.metric.acts c,?_,?_⟩
  · intro x i
    have h {K : Packet 1 Faces} {v : ℝ} (h : Folded σ K v) :
        Summable (fun z:Cover=> K x (fun _=> (z,i))) := by
      have H : Injective fun z:Cover=> ((z,i):Market Faces) := fun _ _ he=> congr_arg Prod.fst he
      have he := (bill_folded x hσ h).comp_injective H
      exact he
    change ∑' z,(saddle Y.metric x (fun _=>(z,i))-saddle H.metric x (fun _=>(z,i)))=0
    rw [Summable.tsum_sub (h hy) (h hh), saddle_sum,saddle_sum,sub_eq_zero]
    apply Complex.ofReal_injective
    rw [roadSum_price,roadSum_price,hY.starts,hH.starts]
  · change plain Y.metric _ _ - plain H.metric _ _ = _
    rw [pass_one Y.metric x y u,pass_one H.metric x y u]; rfl
  · rw [mul_add]; exact (ticket_folded ..).1 (((ticket_folded ..).2 hy).sub ((ticket_folded ..).2 hh) (by positivity) (by positivity))
  · intro x y
    change display (fun x y=> plain Y.metric x y-plain H.metric x y) _ x y = _
    rw [display_sub x y (cost_any (plain0 hp (le_refl _)).1 hσ _) (cost_any (plain0 hq (le_refl _)).1 hσ _), matches_plain Y.metric x y,matches_plain H.metric x y]
    rfl
  unfold quadratic Precision.K
  rw [Matrix.mul_sub,Matrix.sub_mul]
end YM.RG08.Flat
