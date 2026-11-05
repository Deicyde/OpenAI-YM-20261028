import YM.Further.DENSE_MIXED_KERNELS.Palette
import YM.MergeProof.Cachet
import YM.MergeProof.Domino
import YM.MergeProof.Wallet
import YM.MergeProof.Wicket
import YM.Next.RANK.SealMix
import YM.Next.RANK.Stall
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term

/-! All gas labels pi beyond repr.Same signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Push GridApprox.Nil Motion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V][Fintype V]{n:Side}{G:Gauge}(o:V→Site n) {Q:Rep G n} {e:ℝ}
lemma peel (F: Box n→ veil V)(S:Support n)(hf:∀ i:Box n, F i≠0 → Sure i): Accent.field F S= ∑ i:Finset (Neat n),peeled id (fun i:Neat n=>F i.val) S i:=by
   let T: Neat n ↪ Box n:=⟨Subtype.val,Subtype.val_injective⟩; let A:= (Finset.univ: Finset (Finset (Neat n))).image (fun i=> i.map T)
   have hu (i : Finset (Box n)) (hi:i∉ A): grid F S i=0:=by
      unfold grid;split; next h=>
         by_contra hQ; let U:=i.preimage T T.injective.injOn; have he : U.map T=i:=by
            ext j; constructor
            · intro h; obtain ⟨u,hu,rfl⟩:=mem_map.mp h; exact Finset.mem_preimage.mp hu
            intro h; let u:Neat n:= ⟨j,hf j (fun he=>hQ (Finset.prod_eq_zero h he))⟩; exact mem_map.mpr ⟨u,Finset.mem_preimage.mpr h,rfl⟩
         exact hi (mem_image.mpr ⟨_,mem_univ _,he⟩)
      rfl
   unfold field; rw [← Finset.sum_subset (subset_univ A) (fun i _=> hu i)]; unfold A; rw [sum_image (fun _ _ _ _ h=> Finset.map_injective T h)]; refine sum_congr rfl fun i _=>?_
   have hp: (i.map T).biUnion (fun j=>j.2)=i.biUnion fun j=>j.val.2:=by ext j; simp [T]
   have he: Pattern S (i.map T)↔ ripe id i S:=by
      constructor
      · rintro ⟨h,h'⟩; exact ⟨fun i hi j hj hij=>h (mem_map_of_mem _ hi) (mem_map_of_mem _ hj) (T.injective.ne hij),hp.symm.trans h'⟩
      rintro ⟨h,h'⟩; refine ⟨fun j hj i hi hv=> ?_,hp.trans h'⟩; obtain ⟨j,hj',rfl⟩:=mem_map.mp hj; obtain ⟨i,hi',rfl⟩:= mem_map.mp hi; exact h hj' hi' fun h=> hv (congr_arg _ h)
   unfold grid peeled; exact if_congr he (prod_map i T F) rfl
lemma beacon (A:Activities G n) (Z : ℕ→ Config G n→ℂ)(i : Box n) (hi : ¬ Sure i) (U : Config G n): profile A Z i U=0:=by
    haveI : IsEmpty {j // barcode A j=i}:=⟨fun ⟨j,h⟩=>hi (h ▸ (sender A j).property)⟩
    unfold profile cram; rw [tsum_empty]
variable {d:ℕ}{F:Labels.Frame G d} (D:V → Coefficient F n)
variable {H:Hol G}(hq:∀ i,(D i).Format 0 H Q) (s:V→Signed)(x:V→Prop)
def dye (s:Signed)(x:Prop):Motion:=(s,decide x)
variable (β:ℂ) (hb:star β=β)
lemma calling (z:Signed)(x:Prop)(c:ℂ):scalar (dye z x) c=dot x c:=by unfold Motion.scalar dye dot; simp
include hb
lemma flags_dot (z:Signed)(x:Prop)(c:ℂ): β*scalar (dye z x) c=dot x (β*c):=by rw [calling]; unfold dot; split<;> simp [hb,mul_comm]
omit hb
lemma glide_sent (s:Signed)(x:Prop)(y:Site n)(i:Neat n): (sent s y i).val=puff (dye s x) y i.val:=by
    rw [sent_one]; unfold puff; change _=(sky _ _ _, sky _ _ _); rw [shading,shading]; rfl
lemma foam_org {F0:Coefficient F n}(i:Neat n)(U): foam F0 Q i U=profile Q.activities F0.forced i.val U:=by
    rw [profile, expand_eq]; refine tsum_congr fun j=>?_ ; have hx : identifier Q j=i ↔ barcode Q.activities j=i.val:=Subtype.ext_iff; dsimp only; split; next he=> rw [if_pos (hx.mp he)]
    next he=>rw [if_neg (hx.not.mp he)]
-- sum CHIPS
variable {B: Neat n → Burst G n Q.p.threshold}
local notation "A"=> Q.activities
local notation "Y"=>bits o D β hq s x
set_option quotPrecheck false
local notation "g!" => fun m=> sunny Q (D m).forced (dye (s m) (x m)) (o m) β
include hb
lemma dye_wash (m:V)(i : Neat n)(U): (∑ j:Rootage n, if attached (Y m j)=i then (Y m j).amount U else 0)= Poly.send (slot m) ((g! m) i.val U):=by
    let b:=o m; let T:= dye (s m) (x m); let t:=sent (s m) b; obtain ⟨i,rfl⟩:= t.surjective i
    have he : ((g! m) (t i).val U)=dot (x m) (β*foam (D m) Q i (pull (s m) b U)):=by
       rw [foam_org, show (t i).val=_ from glide_sent (s m) (x m) _ i]; unfold sunny; dsimp only; simp only [b,Pi.smul_apply,floatUp, Equiv.symm_apply_apply,smul_eq_mul]; unfold stepUp; exact flags_dot β hb _ _ _ -- edit implicit
    rw [he]; unfold bits; simp_rw [seal_chip]; change ∑ j:Rootage n,(if t j.val=t i then _ else 0)=_
    by_cases h:0∈i.val.1
    · rw [Finset.sum_eq_single (⟨i,h⟩:Rootage n),if_pos rfl]; rfl
      · intro j _ hj; rw [if_neg (fun hx=> hj (Subtype.ext (t.injective hx)))]
      simp
    rw [Finset.sum_eq_zero (fun j _=> if_neg (show t j.val ≠ t i from fun hh=> h (t.injective hh ▸ j.property))),dusted (hq m) _ h,mul_zero,dot_zero,Poly.send_zero]
end YM.MergeProof.Accent
