import YM.RG05Readout.Address.Token
/-!
# Lower test weights transmitted with field degrees

Exact transfer keeps finite projection cut through joint weight. From the ν>μ
outputs the only contribution at/below a specified weight k comes from scalar
strictly lower integration rows of Q.x. Those rows are furnished by a further
priced actual transfer. At μ itself keep the complete inherited input-axis row.
Plus Attainment tickets to the weighted price `Ride` on all marks. The final
relation does NOT propagate arbitrary equivalences inside a polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α C' :ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
local notation "K0"=>K^3
include hp h hm hx hδ
variable (k:Letter d)(a:ℕ) (Q:Coefficient (C.labels.level (kept k)) (C.side m p)) (y:Three G (C.side (m+1) p)) (o:Site (C.side (m+1) p))
local notation "W"=> F (kept k)
local notation "Si"=> invoice Q 0 (S (kept k)) R
local notation "q"=> Q.x
local notation "ϵ"=> (W).coeffSize q
local notation "χ"=> (((L).val:ℂ)^(kept k))
local notation "Rt"=> (↑(ℓ^depth k):ℂ)
local notation "ε"=> Native.readJ k δ
local notation "P₀"=> Travel C N m p d o D
variable (hZ: Q.Format 0 C.params (C.path.rep N p m))(hP: Q.remBound 0 (C.path.rep N p m) (kappa C.path m) t)
    (ht: Ride (C.path.levels.clock.op m p) o 0 D (((C.path.S.block m).val:ℂ)^(kept k)) y (invoice Q 0 (C.localSection (kept k)) (C.path.rep N p m)) u)
include hP hZ ht
-- price all guesses in canonical Laurent branch extension. U scalars from knot inputs separately
structure Course (I:Tape G (C.side (m+1) p)) (Zs:Tape G (C.side m p))(x z:Palette C d) (w s:ℝ):Prop where
    paid : Printed C d R 0 (κ m) Zs x z w
    ready : Travel C N m p d o D I Zs s
set_option maxHeartbeats 400000 in
lemma raising (i:Letter d) (H:∀ j:ℕ,j < a → (W).coeffSize (basisCut W j q)≤α)(hα:0≤α) : let f:= (ε) (line i); let po:=(Rt) • glyph (f • readJ i 0) y
    let U:=K^3*ϵ; let A':=K^2*(2*K*ϵ+t)
    ∃ V:Tape G (C.side m p),∃ x z:Palette C d, Course (D:=D) o po V x z A' (K^3*(u+K*ϵ))∧ size x≤U∧ (if i=k then x=chunk k q else size (clear C d (depth k+a) x) ≤ K^3 * α) :=by -- NaturalCost remove
   intro f P U A'
   have hn:0 < K:= lt_of_lt_of_le zero_lt_one hp.fits
   have hx':‖f‖≤ K*K:= (fees d k hδ (hp.card i)).trans (mul_le_mul_of_nonneg_right hp.earns hn.le)
   have hT := ht.nonneg; have hnn:= rem_nonneg hP; have ht : Ride Z o 0 D χ y Si u:=ht
   have hW:0 ≤ ϵ:=Work.G08.size_nonneg ..; let A:=R; have hZ := hZ
   let a₀:=hp.sense d le_rfl; have hp': Priced d (f • readJ i 0) (K^3):=by
       have hu:=cappay d (readJ i 0) f (show Priced d _ _ from fun _ _ hz=> fees d i box0 hz)
       intro φ t ht; exact (hu φ t ht).trans (mul_le_mul_of_nonneg_right ((mul_le_mul hx' hp.earns (feepos _|>.le) (by positivity)).trans_eq (by ring)) ht.nonneg)
   by_cases hV:i=k
   · subst i; have hv:f=1:=by unfold f; rw [sliceC k k δ le_rfl, if_pos rfl]
     unfold P; rw [hv,one_smul]; rw [hv,one_smul] at hp'
     let V:= glyph (readJ k 0) Si
     have hj := (Travel.scaleTo y _ (readJ k 0) hp' k ht)  
     have hr : Travel C N m p d o D (Rt • glyph (readJ k 0) y) V (K^3*u):=hj
     have hy : t ≤ A':= (le_mul_of_one_le_left hnn (show 1≤ K^2 from one_le_pow₀ hp.fits)).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (pow_nonneg hn.le _))
     have hl:= printed_one k Q hZ hP
     refine ⟨V,_,_,⟨hl.grow hy,hr.extend ?_⟩,?_,?_⟩
     · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hn.le hW)) (pow_nonneg hn.le _)
     · rw [size_chunk]; exact le_mul_of_one_le_left hW (one_le_pow₀ hp.fits)
     rw [if_pos rfl]
   by_cases he:depth k<depth i
   · let F':=C.labels.level (kept i); have hi:kept i ≤ kept k:= by unfold kept;omega
     obtain ⟨T,hB,hC,hR,hX,hI⟩:= Cursor.reshape (D:=D) h hm hp Q hi (Nat.sub_le ..) hx hZ hP ht
     let V:= glyph (f • readJ i 0) (invoice T 0 (C.localSection _) R)
     have heq: V=f • glyph (readJ i 0) (invoice T 0 (C.localSection _) R):=by ext1 q₁; exact smul_assoc f ((readJ i 0) q₁) (invoice T 0 (C.localSection _) R)
     have hh:Travel C N m p d o D P V (K^3*(u+K*ϵ)):=Travel.scaleTo y _ _ hp' k hR
     let x:=chunk i T.x; let s:=f • x; have ht': Printed C d R 0 (κ m) (glyph (readJ i 0) (invoice T 0 (S (kept i)) R)) x _ (K*ϵ + (0+K*ϵ) + t) := printed_one i T hB hC
     refine ⟨V,s,f • chunk i (Trace.Physical.Germ.projection _ C.params (R).p.threshold 0 T),⟨?_,hh⟩,?_,?_⟩ -- order
     · rw [heq]; refine (ht'.twist a₀.order a₀.power f).grow ((mul_le_mul_of_nonneg_right hx' ht'.nonneg).trans_eq ?_); unfold A'; ring
     · unfold s; rw [size_smul, size_chunk]; apply (mul_le_mul hx' hX (Work.G08.size_nonneg ..) (mul_nonneg hn.le hn.le)).trans_eq; unfold U; ring
     rw [if_neg hV]; change size (Address.clear C d (depth k+a) (f • chunk i T.x))≤ _; rw [map_smul,cpart]
     split
     next hz =>
       let u₁:=depth k + a - depth i
       rw [size_smul,size_chunk]; apply (mul_le_mul hx' ((hI u₁).trans (mul_le_mul_of_nonneg_left (H u₁ (by unfold u₁;omega)) hn.le)) (Work.G08.size_nonneg ..) (mul_nonneg hn.le hn.le)).trans_eq; ring
     next => rw [smul_zero,size_zero]; exact mul_nonneg (pow_nonneg hn.le _) hα
   have hf : f=0:= by unfold f; rw [sliceC k i δ (Nat.le_of_not_gt he), if_neg (Ne.symm hV)] -- depth requirement reversed? lhs depth i <=k
   unfold P; rw [hf]; simp only [if_neg hV,zero_smul]
   have h_zero : glyph (0:PulseC) y=0:= LinearMap.ext (fun i=> zero_smul ..); rw [h_zero,smul_zero]
   refine ⟨0,0,0,⟨Printed.grow (Printed.blank (Real.sqrt_pos.mpr (forcedPos ..))) ?_,Travel.vac ?_⟩,?_,?_⟩
   · unfold A'; positivity
   · positivity
   · rw [size_zero]; unfold U; positivity
   rw [map_zero,size_zero]; positivity

end YM.RG05Readout.Address
