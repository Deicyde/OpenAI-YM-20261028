import YM.FullVolume.Fire
import YM.FullVolume.Ocean
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p n N : ℕ}

variable (R : Weave G)
private lemma additive (I : Finset (Fin n)) (f : Fin n→Pre G) {r m : ℕ} (hf : ∀ i∈I,Continuous (f i))
    (h : ∀ i∈I,MicroAt (f i) r m) : MicroAt (∑ i∈I,f i) r m := by
  induction I using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact MicroAt.zero G r m
  | insert i s hi ih=>
    rw [Finset.sum_insert hi]
    let a := Finset.mem_insert_self i s
    have he : Continuous (∑ j∈s,f j) := by
      rw [funext (fun x : CoverConfig G=> Finset.sum_apply x s f)]
      exact continuous_finsetSum _ fun j hj=> hf j (Finset.mem_insert_of_mem hj)
    apply (h i a).add _ (hf i a) he
    exact ih (fun i hi=>hf i (Finset.mem_insert_of_mem hi)) (fun i hi=>h i (Finset.mem_insert_of_mem hi))

private lemma radius_uniform {B : Frame G d} {H : Hol G} (X : SectionData B) (he : Portfolio H X (R d)) :
    ∃ r m : ℕ,∀ x : Label G d,x∈Maxwell.equationIdeal G d → MicroAt (X.evaluate (B.coords (R d x))) r m := by
  let S := Maxwell.equationIdeal G d
  have hp {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P : Submodule ℂ V) :
      Module.Free ℂ P ∧ Module.Finite ℂ P := ⟨inferInstance,inferInstance⟩
  haveI := (hp S).1; haveI := (hp S).2
  let E := Module.finBasis ℂ S
  let f : S →ₗ[ℂ] Pre G := ((X.eval_linear).mk' X.evaluate).comp
    (B.coords.toLinearMap.comp ((R d).toLinearMap.comp S.subtype))
  choose r m h using fun i=> (he.rank (E i).1 (E i).2).2
  let M := Finset.univ.sup m
  let A := Finset.univ.sup r
  refine ⟨A,M,fun x hx=>?_⟩
  let z : S := ⟨x,hx⟩
  change MicroAt (f z) _ _
  rw [← E.sum_repr z,map_sum]; simp_rw [map_smul]
  refine additive _ _ ?_ ?_
  · intro i _; apply Continuous.const_smul; exact (he.rank (E i).1 (E i).2).1
  intro i hi; exact ((h i).mono (Finset.le_sup (s:=Finset.univ) (f:=r) hi) (Finset.le_sup (s:=Finset.univ) (f:=m) hi)).scale (E.repr z i)

open FullVolume YM.MergeProof Cells
private lemma clearance (k r:ℕ): ∀ᶠ i:ℕ × ℕ in FullVolume.mesh, ∃ h:k ≤ i.1, 2*r+2 < (C.S.toDepth h i.2).count.val:=by
  have hv:∀ᶠ N in atTop, C.S.a N*(2*(r:ℝ)+2)< C.S.a k:= by
    have hx:= (C.S.shrinks.mul_const (2*(r:ℝ)+2)); rw [zero_mul] at hx; exact hx.eventually (gt_mem_nhds (C.S.a_pos _))
  filter_upwards [FullVolume.deepen.eventually hv, FullVolume.deepen.eventually_ge_atTop k] with i hi hk
  refine ⟨hk,?_⟩; have he:= C.S.embeds_scale (C.S.toDepth hk i.2); rw [he.symm] at hi
  exact_mod_cast (lt_of_mul_lt_mul_left hi (C.S.a_pos _).le)
private lemma clear {k i j r:ℕ}(h:k ≤ i)(hd: 2*r+2< (C.S.toDepth h j).count.val) : (Mark.Outer r (0:Site (C.side i j)))ᶜ ⊆ (Cells.center C.S j h 0).chamber 0:=by
  intro y hy
  let B:= Cells.center C.S j h 0
  have h0:= Stock.centered_margin j h (0:Site (C.side i j)); let z:= Lattice.lift (y-0)
  have hp : ∀ u:Axis, (z u).natAbs < (C.S.toDepth h j).count.val/2:= by
    have hz: separation y 0 ≤ r:= Nat.le_of_not_lt hy
    intro u; have h:= (component_le (y-0) u).trans hz; unfold z; omega
  have ht:= Tiling.fits_stencil _ h0 hp; unfold z at ht; simpa using ht

theorem hole (V:SectionData (C.labels.level d))(he:Portfolio C.params V (R d))(M:C.Makes) (a:Rowe C d) (h:∀ i:ℕ × ℕ, (C.factory d i.1 i.2).terminal (a i) ∈ carrier C R d i.1 i.2):
    Owed (hallmarks V a) 0:=by
  classical
  let Z:= hallmarks V a
  have ht:= innerRegion V he.valid a
  obtain ⟨s,H,hH⟩ := radius_uniform R V he
  refine ⟨ht, Eventually.of_forall (fun k=> ?_)⟩
  filter_upwards [clearance (C:=C) k s, ht.at_origin k, FullVolume.deepen.eventually (lengths C.S H)] with w hi ht hy
  obtain ⟨hn,hv⟩:=hi; obtain ⟨hk,hA⟩:=ht
  let i:=w.1; let p:=w.2; let S:= C.side i p
  let b:= C.beta i p; have hb:= (Overlay.beta_positive (N:=i) (p:=p) M.wilson (le_refl _)).ne'
  let o:= (0:Site S); let f:= Z i p 0; let X:=Cells.center C.S p (show k ≤ i from hn) o
  let L:= Finset.univ.erase (0:X.Cell)
  let t : Config G S→ℂ:=fun U=>∏ j∈L,X.copy j f U
  have hT: Interior (Mark.Outer s o) t:= by
    apply Interior.combines; intro j hj
    apply (X.copies j hA).enlarges; intro y hY; by_contra hp
    have hh : y∈ X.chamber 0:= clear hn hv hp
    exact (Finset.ne_of_mem_erase hj) ((X.which_chamber hY).symm.trans (X.which_chamber hh))
  have ha:=h w; obtain ⟨y,hy',h0⟩:= obtained R _ ha
  have hz : f= ((C.S.a i:ℂ)^d)⁻¹ • (V.evaluate ((C.labels.level d).coords (R d y)) ∘ expandAt o):=by
      unfold f Z hallmarks; unfold embedTo at h0; simp only [LinearEquiv.trans_apply] at h0; unfold initial
      rw [(C.factory d i p).terminal.injective h0]
      let F:= C.labels.level d; let j:= C.path.levels.clock.threshold i; rw [show ∀ w:C.label d,F.scaled j⁻¹ (tied C d i w)=w from (tied C d i).left_inv]; rfl
  have hG: moment b (fun U=> ∏ j:X.Cell, X.copy j f U)=0:= by
      have ht': moment b (fun U=> f U*t U)=0 := by rw [hz]; exact ((hH y hy').scale _) S (hy p) o b hb t hT.localSites ⟨hT.borel,hT.cost⟩
      convert ht' using 2; funext U; exact (by rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0:X.Cell)),X.copy_zero])
  refine ⟨hn,hA,?_⟩
  change X.rootTest b f ≤ 0
  unfold Tiling.rootTest; rw [hG,norm_zero,Real.zero_rpow (by positivity)]
end YM.Push.Mark

namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels FullVolume
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){f:Extraction.Order}{N p d:ℕ}(V:SectionData (C.labels.level d)) (R:Mark.Weave G)
    (hV:Mark.Portfolio C.params V (R d)) {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}(P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)){U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
include H B V R h hV
lemma banked (x:Rowe C d) (hv:Coin C x) (hp:∀ j,x j∈ catalog C R d j.1 j.2 (P j.1 j.2)): Owed (upper C x) (flight C (-(1/32))) := by
   let Z'(i : Cutoffs):= (C.factory d i.1 i.2).terminal; let y:Rowe C d := fun i=> (P i.1 i.2).symm ((Z' i).symm (x i))
   have he(i) : Z' i (P i.1 i.2 (y i))=x i:=by unfold y; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
   have hx(i): Z' i (y i) ∈ Mark.carrier C R d i.1 i.2:=by
      obtain ⟨v,hv,hw⟩:= hp i; change bindP C R d i.1 i.2 _ v = x i at hw; unfold Z' y; rw [← hw,bindP,Astar,LinearEquiv.trans_apply,LinearEquiv.trans_apply, LinearEquiv.trans_apply]; simp only [Z', LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]; exact Mark.entry_mem C R d i.1 i.2 _ hv
   have hy : Sluggish C y := by
     apply ((Sluggish.const (C:=C) (2:ℝ)).mul (carding _ hv)).reduce
     filter_upwards [FullVolume.deepen.eventually h.stamped] with i hi; exact ((Size.norm_le _ _).trans ((hi i.2).2.1 ((Z' i).symm (x i)))).trans (Real.le_norm_self _)
   have hz:= ocean H B V hV.valid h y hy
   change Owed (upper C (fun i=> Z' i (P i.1 i.2 (y i)))-hallmarks V y) _ at hz; rw [show (fun i=>Z' i (P i.1 i.2 (y i)))= x from funext he] at hz
   have hr:= Affords.add H hz (Mark.hole R V hV H y hx); change Affords _ (_ + (0:ℕ→Cutoffs→ℝ)) at hr; rw [add_zero, sub_add_cancel] at hr; exact hr
end YM.MergeProof
