import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Payment
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curtain
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Hearth
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Fees

/-! # Exact kernel revenue on one compulsory component

Positivity test on the real intact sector. Works even with leases of halo
larger than the read stencil. Uses rank-threshold purchase on the reheated
clock (true m-keeps) and exact authentic affine factors, not a postulate from
a cleared estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps AnalyticBridge.Annulus1AD Oriented
open AnalyticNext.ConnectedActivity SectorNext.Remainder
open _root_.YM.SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β u r w d C : ℝ}
section hull
variable (T : Tube G S) (V : Config G c) (O : Stores S) (U : Config G f) (k : S.Choices)

def ceilingE (O : Stores S) (Y : ℕ) := (univ : Finset (Grain S)).filter fun i=> grantPlace S i∈O.dome Y

lemma levy_equ (Y : ℕ) {A : Stores S} (Z : LinkArray G (Frozen A x F)) (q : Chi) (t d : ℝ) (a : Prices G (Active A x F)) :
    let U:= AnalyticBridge.Annulus1AD.landed x A F V Z a; let m:= portrait T A F k x V .endpoint q d Z
    Aff.weight*(∑ i∈ceilingE O Y,levy T x V Z k q d t a i) = averaged fun s=>
      let W:= anchorage (turnStore s O) Y; let U':=pull s 0 U; let V':=pull s 0 V; let k':=choice s k
      Wax.reread T W x t U' V' k'- columns V x k T F A q d Z a s W + columns V x k T F A q d Z m s W := by
  intro U m
  let F₀ (s : Signed):= univ.filter (fun i : Bars S=> grantPlace S (s,i)∈ O.dome Y)
  have hk s (g : Bars S→ℝ) :
      let R:= anchorage (turnStore s O) Y
      (∑ i∈F₀ s,g i) =
        (∑ i∈R.face,g (.inl i))+(∑ i∈R.noise,g (.inr (.inl i)))+
        (∑ i∈R.coarse,g (.inr (.inr (.inl i))))+(∑ i∈R.rows,g (.inr (.inr (.inr i)))):= by
    intro R; unfold F₀ R anchorage; simp_rw [sum_filter]
    change (∑ i : Cell f ⊕ _,_)= _ -- name shadow
    simp_rw [Fintype.sum_sum_type]; simp only [grantPlace,seedPlace,← dome_turn]; abel
  unfold averaged ceilingE Grain; rw [sum_filter, Fintype.sum_prod_type]
  apply congr_arg (Aff.weight * ·); apply Finset.sum_congr rfl; intro s _
  rw [show (∑ i, if grantPlace S (s,i) ∈ O.dome Y then _ else 0)=∑ i∈F₀ s,levy T x V Z k q d t a (s,i) from (sum_filter ..).symm]
  unfold levy; rw [sum_add_distrib,sum_sub_distrib,hk,hk,hk]; dsimp only [outer, Sum.elim_inl,Sum.elim_inr,coinMeter]
  unfold columns Wax.reread; simp only [Finset.sum_const_zero,add_zero]; unfold U m; abel

lemma reinterpret (x r : ℝ) (D : ℕ) (hD : 2≤D) :
    Wax.reread T (anchorage O (D*radiusB x)) x r U V k= Wax.stakeBook T O x r U (S.prediction U k) V + Wax.reread T (bandRows O D (radiusB x)) x r U V k := by
  -- only F face changed from the earlier band_bill. Keep all Lapse anchored
  let X:= anchorage O (D*radiusB x); let Y:= anchorage O (2*radiusB x); let Q:= bandRows O D (radiusB x)
  let f (t : ℝ) (I : Finset (Cell f)) := ∑ i∈I,T.workF (till x) U V t (temp x) i
  let e:=fiery G x S.patch.L
  have hx P : Wax.reread T P x r U V k= P.work T x U k V + f r P.face - f e P.face:=by
    unfold Wax.reread YM.SectorNext.Remainder.Affine.Window.work onWindow f; abel
  have hp : X.work T x U k V=O.assessed T x U (S.prediction U k) V+Q.work T x U k V:= (AnalyticBridge.Annulus1AD.band_bill T O x k U V hD).symm
  have he : Y.face⊆ X.face := fun i hi=> Finset.mem_filter.mpr ⟨mem_univ _,Aff.placed O _ _ (Nat.mul_le_mul_right _ hD) ((mem_filter.mp (show i∈Y.face from hi)).2)⟩
  have h (t : ℝ) : f t Y.face+ f t Q.face=f t X.face:=(add_comm ..).trans (Finset.sum_sdiff he)
  simp_rw [hx]; rw [show (anchorage O (D*radiusB x))=X from rfl,hp]
  unfold Wax.stakeBook; change _=O.assessed T x _ _ _ - f e Y.face + f r Y.face +(Q.work T x U k V+f r Q.face-f e Q.face)
  simp_rw [← h]
  abel
end hull
section
-- at actual candidate call. Avoid threshold from transplanted flags.
structure Hefts (S : StepData c f) (P : Teller G) (x width u δ W : ℝ) : Prop where
  earns (T : Tube G S) : P.Funds S T → 100*(1+radiusB x) ≤ c.val → ∀ (A : Stores S) (F : Forest S.ratio) (O : Stores S) (D : ℕ),
     AnalyticBridge.Annulus1AD.Packet O A D → 205*radiusB x ≤ D → ∀ (V : Config G c) (Z : LinkArray G (Frozen A x F)) (k : S.Choices) q (a : Prices G (Active A x F)),
     let U:= AnalyticBridge.Annulus1AD.landed x A F V Z a; let d:= width*fiery G x S.patch.L
     Seeded A U k V x W → Alive S U k → Next.SectorChange.doors q d (tape a) ≠ 0 →
       δ*u^2*(O.shares:ℝ) ≤ Aff.weight* ∑ i∈ceilingE O (200*radiusB x),levy T x V Z k q d u a i

lemma launched (P : Teller G) {L : Side} {width x m W : ℝ}
    (h : Wax.Peaking P x W m (2*width) L 200) (hL : S.patch.L=L)
    (hs : Seen P L W width (retime x)) (hp : 1≤radiusB (retime x)) (ht : span S.patch (retime x) ≤ radiusB (retime x)/50)
    (he : 0 < width * fiery G (retime x) L) (hE : width*fiery G (retime x) L<firstRadius G)
    (hB : ∀ T : Tube G S, P.Funds S T → 100*(1+radiusB (retime x)) ≤ c.val → Boosted T P (retime x)) :
    Hefts S P (retime x) width (Next.Rank.Paint.phase (betaF G x L)) m W:= by
  constructor; intro T hT hM A F O D hA hY V Y k q a U d hz hv hy
  let u:=retime x; let s:=S; let f' := Next.Rank.Paint.phase (betaF G x L)
  let g := fun s:Signed=> turnStore s O
  rw [levy_equ]; apply le_trans (le_of_eq (av_const _).symm); apply av_mono; intro s
  let P₀:=turnStore s O; let V':=pull s 0 V; let U':=pull s 0 U; let k':=choice s k
  obtain ⟨ℓ,r,hUpt,-⟩:=hT.feeds
  obtain ⟨b,hP⟩:= (hB T hT hM).license A F V hz.exactFlags
  let p := portrait T A F k u V .endpoint q d Y
  let x' := bandRows P₀ 200 (radiusB u); let H':=anchorage P₀ (200*radiusB u); let v:= harvest A O u F s 200; let b':=signedArray u A F q d V Y a s
  have hw : Wide P₀ (turnStore s A) 200 u W U' k' V':=wide_of_seeded _ _ _ _ _ _ _ _ (pull_seeded s (funds_branch hT) hz) (show Alive S _ _ by rw [Alive,(carry s (funds_branch hT) k U).1]; exact hv)
  have hf := harvesting ht (x:=u) (D:=200) (s:=s) (F:=F) hA
  have H := band_bought (D:=200) (B:=radiusB u) (hA.turns s) (by change 205*radiusB u≤_ at hY; omega)
  have hS:= turn_sliced s F U (fun i hi=> F.on_tree _ ⟨i,hi⟩)
  have hg:0<d∧d<firstRadius G:=by unfold d; rw [hL]; exact ⟨he,hE⟩
  have ht' : v.charts U' V' b' (2*width) u:= by
    obtain ⟨K,hK,hk,hS'⟩ := hs
    obtain ⟨w,hw'⟩:= hS' S T hL hM hT 200 (turnForest s F) P₀ _ U' k' V' hS hw
    have hh : admitsHere A O u F q d (tape a) (300*radiusB u)≠0:=Finset.prod_ne_zero_iff.mpr fun i _=> every_door q hy i
    have h' (i) (hi : inSweep P₀ (turnStore s A) 200 (radiusB u) i): PatchInputs U' V' b' (2*width) u i:= preview q V Y a hg.1 hk hg.2 hp hK (by unfold u; omega) hh s i hi w (hw' _ hi)
    exact ⟨fun i hi=> h' _ (H.1 _ (hf.1 hi)),fun i hi=> h' _ (H.2.1 _ (hf.2 hi))⟩
  have hh := (h c f S T hL hM hT P₀ _ (turnForest s F) U' k' V' ((hA.turns s).ownership (by omega)) hw hS x' v hf H b' ht').2
  change _≤ Wax.reread T H' u f' U' V' k'-columns V u k T F A q d Y a s H'+ columns V u k T F A q d Y p s H'
  apply le_trans ?_ (le_add_of_nonneg_right (columns_nonneg ..))
  -- uses true Peaking
  rw [reinterpret T V' P₀ U' k' u _ 200 (by omega), show columns V u k T F A q d Y a s H'=_ from extracting V u k T F A q d Y a s O 200 hUpt hP]
  simp_rw [add_sub_assoc]; rw [show O.shares=P₀.shares from (same_price s O).symm]; exact hh
end
end YM.PhysicalNext.InteractingRank.Milk
