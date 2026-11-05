import YM.RG05Readout.Address.Preimage
/-!
# Leading diagonal for allocation of graph inverse

Only the specified rows of E, which receive the ε estimate. For all others use
pre-L cost bound on raw actual transfer. Thus the candidate shape AFTER field
restrictions isn't declared to be the derivative predicted everywhere.
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
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}
section edges
variable (i:Mark C d)
local notation "F"=> C.labels.level (kept i.1)
def leadLean : Palette C d:=chunk i.1 ((T i.1).map (Size.axis (F) i.2))
lemma lead_pay : leadScale C L i (T i.1)= (chargeN L i:ℂ) • leadLean (T:=T) i:=by
    unfold leadScale leadLean
    let u:= Size.axis F i.2; let t':=(T i.1).map; let h:ℂ:=↑(chargeN L i)
    have hp : vowel F L u=h • u:=by
       funext j; by_cases hz:j=i.2
       · subst j; change (↑((L).val):ℂ)^(kept i.1-((F).grades i.2).1)*u i.snd=h*u i.snd; unfold kept h chargeN weights; rw [Nat.sub_sub]; push_cast; rfl
       unfold vowel u Size.axis; simp [hz]
    have he : (T i.1).leads L u=h • t' u:= by change t' (vowel F L u)=_;rw [hp,map_smul]
    rw [he]; ext1 i'
    by_cases ht:i'=i.1
    · subst i'; rw [chunk_self]; change _=h • chunk i.1 (t' u) i.1; rw [chunk_self]
    simp [chunk_miss _ ht]

lemma triangle_cost1 (j:ℕ) {F': Frame G j}{c:ℝ}(hc:1 ≤ c): c ≤ triangularPrice F' c:=by
    have he: c ≤ c+ (↑(F'.extra+1:ℕ):ℝ)*c^2:=le_add_of_nonneg_right (by positivity)
    have hs:=he.trans (show _ ≤ (c+(↑(F'.extra+1:ℕ):ℝ)*c^2)^(j+1) from by simpa only [pow_one] using pow_le_pow_right₀ (hc.trans he) (show 1≤j+1 from Nat.le_add_left ..))
    exact hs.trans (le_mul_of_one_le_left (zero_le_one.trans (hc.trans hs)) (by exact_mod_cast Nat.le_add_left 1 F'.extra))
include i
lemma leans (hw:Plot D s K c α β T) : let p:= leadLean (T:=T) i
    size p ≤ c ∧ 1 ≤ c * ‖val p i‖ ∧ ∀ j:Mark C d,j≠ i → weights j ≤ weights i → val p j=0:=by
     intro p; obtain ⟨τ,hτ,hk⟩:=hw.star i.1; let v:= Size.axis F i.2
     have hy : τ ≤ c:= le_trans (triangle_cost1 (kept i.1) (F':=F) hτ.lower.price) hk
     have he:= hτ.norm v|>.1; rw [show (F).coeffSize v=1 from Size.size_axis ..,mul_one] at he
     refine ⟨by unfold p leadLean;rw [size_chunk]; exact he,?_,?_⟩
     · unfold val p leadLean; rw [chunk_self]; exact (hτ.lower.diagonal i.2).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
     rintro ⟨j,b⟩ hi hw; unfold val p leadLean
     rcases i with ⟨i,x⟩; by_cases ht:j=i
     · subst j; rw [chunk_self
            ]; by_contra heq
       have hv:=hτ.lower.triangular b x (by rintro hc; subst b; exact hi rfl) heq
       exact (Nat.not_le_of_gt hv) (Nat.add_le_add_iff_left.mp hw)
     change chunk i _ j b=0; simp [ht]
end edges
section cost
lemma on_ticket (i j:Mark C d): val (ticket i) j=if i=j then 1 else 0:=by
   obtain ⟨i,a⟩:=i; obtain ⟨j,b⟩:=j
   unfold val ticket; by_cases h:i=j
   · subst j; rw [chunk_self]; simp [Size.axis, Pi.single_apply,eq_comm]
   rw [chunk_miss _ (show j ≠ i from Ne.symm h), if_neg (fun H=>h (Sigma.mk.inj_iff.mp H).1)];rfl
lemma ticket_self {E:Type*}[AddCommGroup E][Module ℂ E] (i:Mark C d)(z:Mark C d→E): Slide (ticket i) z=z i:=by
    unfold Slide; simp_rw [on_ticket,ite_smul]; simp
lemma echo_bill (L':Side)(X:Mark C d→ Palette C d) (H:∀ i,size (X i) ≤ c*chargeN L' i) (x:Palette C d): size (Slide x X) ≤ c* size (amplify d C L' x):=by
    rw [← charge_sum,Finset.mul_sum,Slide]; apply le_trans (size_sum ..); apply Finset.sum_le_sum; intro i _
    rw [size_smul]; exact (mul_le_mul_of_nonneg_left (H i) (norm_nonneg (val x i))).trans_eq (mul_left_comm ..)
end cost
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "∂"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
-- angular estimates direct/use diagonal reciprocal only. Introduce ideal bend
structure BeamLine (C:Family G)(d:ℕ)(f: Mark C d → Palette C d)(t u:ℝ):Prop where
    pays i:size (f i) ≤ t
    down i:1 ≤ u * ‖val (f i) i‖
    strict (i j:Mark C d):weights j ≤ weights i→j≠i→ val (f i) j=0

lemma bounded_p {X:Mark C d→Palette C d} (h:BeamLine C d X t u)(x:Palette C d) : size (Slide x X) ≤ t*size x:=by
   unfold Slide; apply (size_sum ..).trans; rw [size,Finset.mul_sum]; exact Finset.sum_le_sum (fun i hi=>by rw [size_smul,mul_comm t]; exact mul_le_mul_of_nonneg_left (h.pays i) (norm_nonneg _))
end YM.RG05Readout.Address
