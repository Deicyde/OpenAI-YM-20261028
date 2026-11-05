import YM.MergeProof.Biscuit

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:C.label d)(X:Extra.Histories.Music (C.labels.level d) C.path N p) (Y:(C.labels.level d).Index→ C.label d)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
    (J:ℕ) (K:Stock.Tabs C.path.levels)

lemma modems (he:∀ i: (F).Index,(F).coeffSize (Size.axis F i-(X.tone k).index (Y i)) ≤ (1:ℝ)/4) :∃ t:C.label d,L=∑ i,t i • Y i∧ (F).coeffSize t ≤ 2*(F).coeffSize ((X.tone k).index L):=by
   let I:=s!; let J:= (X.tone k).index; let V:= (F).Coeff; let A:(F).Coeff →ₗ[ℂ] (F).Coeff:=
      { toFun:=fun v=> ∑ i,v i • J (Y i)
        map_add':=fun v w=>by simp [add_smul,Finset.sum_add_distrib]
        map_smul':=fun v w=> by simp [Finset.smul_sum,mul_smul] } -- syntax
   have h(v:V): (F).coeffSize v ≤ 2*(F).coeffSize (A v):=by
      have hp: v-A v=∑ i,v i • (Size.axis F i-J (Y i)):=by simp_rw [smul_sub,Finset.sum_sub_distrib, show ∑ i,v i • Size.axis F i=v from GridApprox.coeff_sum C v]; rfl
      have hx: (F).coeffSize (v-A v) ≤ (F).coeffSize v / 4:=by
         rw [hp]; refine (Size.finite F _ _).trans (le_trans (Finset.sum_le_sum fun i _=> show (F).coeffSize _≤ ‖v i‖*(1/4) from ?_) ?_)
         · rw [Size.smul]; exact mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)
         rw [←Finset.sum_mul]; unfold Labels.Frame.coeffSize; linarith only
      linarith only [Work.G08.size_triangle F v (A v),hx,Work.G08.size_nonneg F v]
   have hI : Injective A := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x e=> by apply Work.G08.size_separates; simpa [e,Labels.Frame.coeffSize] using h x)
   let t:= L; obtain ⟨v,hv⟩:= LinearMap.injective_iff_surjective.mp hI (J t); refine ⟨v,?_,?_⟩
   · have hh': ∑ i,v i • Y i=t:= J.injective (by rw [map_sum]; simp_rw [map_smul]; exact hv)
     exact hh'.symm
   exact (h v).trans_eq (congr_arg (fun p : V=>2*(F).coeffSize p) hv)
end YM.MergeProof.Accent
