import YM.MergeProof.Garnish
import YM.MergeProof.North.Stained
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Deck
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [DecidableEq I][DecidableEq J][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable (D:Deck V I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)
open Ac Extra.Multi
variable [Fintype I][Fintype J]
variable (w:Name V→ℝ)(u:V→ℝ)
structure Rated (b:ℕ)(e g:ℝ):Prop where
   hires : ∃ G:I⊕J→ℝ,(∀ i,0≤G i)∧(∀ i U,‖D.toll i U‖ ≤ G i)∧Hit D.cover b (fun i=>Poly.toll w (D.mode_ i)*G i) e g
include h
lemma carries (d e g:ℝ)(b:ℕ)(hP:D.Rated w b (d+e) g)(he:0 ≤ d)(hw:∀ i,0<w i)(hu:∀ i,u i= w (i,false)*w (i,true))(hS: ((b+b+1:ℕ):ℝ)^4*g ≤ e) :
    Towed u id (D.sky t) b d (Real.exp g-1) ∧ Towed u Prod.fst (D.clay t) b d (Real.exp g-1):=by
   obtain ⟨H,hH,hR,hG⟩:=hP.hires
   let A(i):= Poly.toll w (D.mode_ i)*H i; let Y:= fun i:D.Quills=>∏ j∈D.glyph i,A j
   have hA i :0≤A i:=mul_nonneg (Poly.worth hw _).le (hH _)
   have hy i : 0 ≤ Y i:=prod_nonneg fun j _=>hA j
   have yh (i:D.Quills): Loci u (D.leaf t i) (Y i):=by
      let M:=∏ j∈D.glyph i,H j; have hp:0≤ M:=prod_nonneg fun _ _=>hH _
      unfold Y A; rw [Finset.prod_mul_distrib, ← Extra.Trajectories.toll_union _ _ (D.run i).buys w, afford _ (D.run i).ready w u hu] -- unfold quip
      refine satin _ _ _ hp fun U=>?_ ; have he : ‖D.bud U i‖≤M:= by unfold bud; rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>hR _ _)
      cases i
      next i=> exact he
      next i=> change ‖D.nectar t U i‖ ≤ M; unfold nectar; split; exact he; rwa [norm_zero]
   have hg:= tsum_nonneg ((hG 0).1) |>.trans (hG 0|>.2.2)
   have hY : Hit (D.reach ∘ D.glyph) b Y d (Real.exp g-1):=by
      intro i; refine Budget.pull_le (q:=D.glyph) (p:=fun _=>True) (forest_price D.cover b he hA hG hS hg i) (fun j=> by split; exact mul_nonneg (hy _) (Real.exp_pos _).le; exact le_rfl) (fun _ _=>trivial) D.tale.injOn (fun j _=>?_)
      split; next hp=> exact le_of_eq ((mul_comm ..).trans (if_pos ⟨D.spark _ (D.run j).fire _ h,hp⟩).symm)
      exact (forest_price D.cover b he hA hG hS hg i).1 _
   have hh i:0 < u i:=by rw [hu]; exact mul_pos (hw _) (hw _)
   constructor
   · refine towing (fun i:D.Paper=>D.reach i.val) _ ⟨Y ∘ Sum.inl,Summable.of_finite,fun i=>?_,fun i=>yh (.inl i)⟩ hh
     exact Budget.pull_le (q:=Sum.inl) (p:=fun _=>True) (hY i) (fun i=>(hY _).1 (Sum.inl i)) (fun _ _=>trivial) Sum.inl_injective.injOn (fun j _=> le_rfl)
   refine towing (fun i:D.Ink=>D.fuse i.val) _ ⟨Y ∘ Sum.inr,Summable.of_finite,fun i=>?_,fun i=>yh (.inr i)⟩ hh
   exact Budget.pull_le (q:=Sum.inr) (p:=fun _=>True) (hY i) (fun i=>(hY _).1 (Sum.inr i)) (fun _ _=>trivial) Sum.inr_injective.injOn (fun j _=> le_rfl)
end YM.MergeProof.Ribbons.Deck
