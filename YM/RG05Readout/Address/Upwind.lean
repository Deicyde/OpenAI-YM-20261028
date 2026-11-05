import YM.RG05Readout.Address.Angular
/-!
# Real angular test with script weights
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ A c t u:ℝ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "δ"=> displacement C p m
local notation "L"=> C.path.S.block m
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "∂"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
local notation "U"=> Palette C d
local notation "J"=> Mark C d
local notation "N₀"=> (Fintype.card (Mark C d):ℝ)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}

/-- Pre-side angular costs. A negative-first block is zero. -/
def clipPrice (n d:ℕ)(t u:ℝ):= n*(u*(1+n*t))^(d+1)
lemma BeamLine.expanded {q:Mark C d→Palette C d}(h:BeamLine C d q t u)(hp:1 ≤ u)(hr:0 ≤ t)(x:Palette C d):
    size x ≤ clipPrice (Fintype.card (Mark C d)) d t u * size (Slide x q) :=by
    let V:=Slide x q; let P:=u*(1+N₀*t); have hU:=size_ge V; have hf:1 ≤ P:= one_le_mul_of_one_le_of_one_le hp (le_add_of_nonneg_right (by positivity))
    have hu := zero_le_one.trans hp
    have H(n:ℕ) :∀ i:Mark C d,weights i < n → ‖val x i‖ ≤ P^n*size V:=by
       induction n with
       | zero=>simp
       | succ n ih =>
           intro i hi; let f(j:J):=val x j*val (q j) i
           have hK j (hj:j∈Finset.univ.erase i): ‖f j‖ ≤ P^n*size V*t:=by
              have hh:i≠j:= Ne.symm (Finset.ne_of_mem_erase hj)
              by_cases h' : weights j < weights i
              · unfold f; rw [norm_mul]; exact mul_le_mul (ih j (by omega)) ((each_price ..).trans (h.pays j)) (norm_nonneg _) (by positivity)
              unfold f; rw [h.strict j i (Nat.le_of_not_lt h') hh,mul_zero,norm_zero]; positivity
           let g:=∑ j∈ Finset.univ.erase i,f j; let s:=size V
           have ht: ‖g‖ ≤ N₀*(P^n*s*t):= by apply (norm_sum_le ..).trans; apply le_trans (Finset.sum_le_sum hK); rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (by positivity)
           have he : f i=val V i -g:=by
               rw [eq_sub_iff_add_eq,show f i+g=∑ j,f j from Finset.add_sum_erase _ f (by simp)]
               change _ = (∑ j, (val x j) • q j) i.1 i.2
               rw [Finset.sum_apply, Finset.sum_apply];rfl
           have hj :=h.down i; calc ‖val x i‖ ≤ u*‖f i‖ :=by rw [show f i=val (q i) i*val x i from mul_comm .., norm_mul, ← mul_assoc]; exact le_mul_of_one_le_left (norm_nonneg _) hj
                                     _ ≤ u*(P^n*s+N₀*(P^n*s*t)):= by rw [he]; exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add ((each_price ..).trans (le_mul_of_one_le_left hU (one_le_pow₀ hf))) ht)) hu
                                     _ = _:= by unfold P s; ring
    apply (Finset.sum_le_sum (fun i (_:i∈@Finset.univ J _)=> H (d+1) i (Nat.lt_add_one_of_le (capped i)))).trans_eq; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];exact (mul_assoc ..).symm

structure Contour (C:Family G)(m d:ℕ)(t u r:ℝ)(A:Palette C d→ₗ[ℂ]Palette C d): Prop where
     sails : ∃ Z':Mark C d → Palette C d,BeamLine C d Z' t u ∧ ∀ x, size (A x-Slide (amplify d C (C.path.S.block m) x) Z') ≤ r*size x

lemma size_compare (x y:Palette C d): size x ≤ size y+size (x-y) := by
      calc _ = size (y+(x-y)):= congr_arg size (add_sub_cancel ..).symm
           _ ≤ _:= size_add ..
lemma size_turn (x y:Palette C d): size (x-y)=size (y-x):=by rw [←size_neg (y-x),neg_sub]
lemma Contour.earns {A:Palette C d→ₗ[ℂ]Palette C d}{Q:ℝ}(h: Contour C m d t u γ A)(ht:0≤t)(hu:1≤u)(he : 0 ≤ γ) (hx:clipPrice (Fintype.card (Mark C d)) d t u ≤ Q)(hz :0 ≤ Q)(hv:Q*γ ≤ 1/2) (x: Palette C d):
    size (amplify d C L x) ≤ 2*Q*size (A x) ∧ size (A x) ≤ (t+γ)*size (amplify d C L x):=by
    let T: Palette C d→ₗ[ℂ]Palette C d:=amplify d C L; obtain ⟨B,hB,H⟩:=h.sails; specialize H x
    let z:= Slide (T x) B; let p:=size (A x); let w:=size (T x)
    have hQ:= (hB.expanded hu ht (T x)).trans (mul_le_mul_of_nonneg_right hx (size_ge _))
    have hj: size z ≤ p + γ*w:= by apply (size_compare z _).trans; apply add_le_add_right; rw [size_turn]; exact H.trans (mul_le_mul_of_nonneg_left (size_refund ..) he)
    constructor
    · have hF : w ≤ Q*p+(1/2)*w:=by
          apply hQ.trans ((mul_le_mul_of_nonneg_left hj hz).trans _); rw [mul_add, ← mul_assoc Q]; exact add_le_add_right (mul_le_mul_of_nonneg_right hv (size_ge _)) _
      change w ≤ 2*Q*p; linarith
    · rw [add_mul]; exact (size_compare (A x) z).trans (add_le_add (bounded_p hB _) (H.trans (mul_le_mul_of_nonneg_left (size_refund ..) he)))
end YM.RG05Readout.Address
