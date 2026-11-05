import YM.FullVolume.Umbra.Scale
import YM.FullVolume.Umbra.Every
import YM.FullVolume.Umbra.Belles
-- one real mark among any two epoch carpets at the same stamp
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
open Lotus
open Draft
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c} {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K} {F₁:BatchK H}{δ δ':ℕ→ Molecule S→ℝ}{Δ Δ':ℕ} (h:Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) δ Δ) (hq: Seats T (F₀:=F₁) (χ:=χ) (M:=M) (j:=j) δ' Δ') {k:Wing}(hm:Rhyme F₀ F₁ k)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop) (m:Molecule S)
open Daisy Charity
set_option quotPrecheck false
-- Aurora; no herd. typed Pourings.
local notation "c'"=> fun n y V=> color (F₀ n) (I n) χ V y
local notation "c''"=> fun n y V=> color (F₁ n) (T n) χ V y
local notation "X₀"=>fun n y (p:(I 0).Chapter) V=>(I n).cologneMill (c' n y V) p
local notation "X₁"=>fun n y (p:(I 0).Chapter) V=>(T n).cologneMill (c'' n y V) p
local notation "m₀"=>fun n y (p:(I 0).Chainbook) V=>(I n).smilesMill V (c' n y V) p
local notation "m₁"=>fun n y (p:(I 0).Chainbook) V=>(T n).smilesMill V (c'' n y V) p
variable (hs:Sweep K) (hp:Sweep H)
include I h R hs
lemma tipJ : Back X₀:=by
     obtain ⟨b,hb,hB⟩:= Draft.cologne I R hs
     obtain ⟨f,hf,hL⟩:= resource I R h hs
     let p:(I 0).ThickP ↪ Molecule S:= ⟨Subtype.val,Subtype.val_injective⟩; let v n (u:(I 0).Chapter):= Sum.elim (fun x=>δ n (p x)) (f n) u
     refine ⟨_,hb.tug (show Sparse v from Sparse.either (h.bud.pull p) hf),fun n u V=>?_⟩
     have ht: |X₀ n (0:ℝ) u V| ≤ b n u:=by
         change |(I n).cologneMill (color (F₀ n) (I n) χ V 0) _| ≤ _; rw [color0]; exact hB ..
     let F:= F₀ n; rcases u with u|u
     · let f y:= color (F₀ n) (I n) χ V y u.val; change priceJ f _
       let s:= F.lotus (K n).tubes x χ o.K W o.a Q.table Q.halo V u.val; have hp: HasDerivAt f s 0:=by simpa [f,s,color] using (((hasDerivAt_id' (0:ℝ)).mul_const (s)).const_add ((I n).spawn χ V u.val))
       refine ⟨hp.differentiableAt,?_⟩;rw [hp.deriv];exact add_le_add ht (lotus_bound I R h u.val n V)
     let z:=matin F (I n) u χ; let B'(Y):=masked (Pressure.temp x) ((I n).bookFoot (.inr u)) z Y; let Z y:=- (I n).trainedMill (c' n y V) u; change priceJ Z _
     have hp: HasDerivAt Z (-B' V) 0:= (scatterC F (I n) (R n|>.N) u V).neg
     refine ⟨hp.differentiableAt,add_le_add ht (show |deriv Z 0|≤ f n u from ?_)⟩
     let S:= locus F (I n) 0 u; rw [hp.deriv, abs_neg]; unfold B'; rw [← mask_ag _ _ _ _ _ _ (0:Site c)]
     by_cases he: Healthy (Pressure.temp x) S V
     · rw [masked_eq _ _ _ _ he]; exact (hL u n V 0 he ℝ (fun _=>V) 0 rfl ⟨(R n).N.position.le,fun i=> a_oneB _ _ (R n).N.position.le⟩).bound
     rw [masked_ne _ _ _ _ he,abs_zero]; exact hf.value ..
omit hs
include T P' hM hm hq
lemma colorJ (m:Molecule S) (V:ℕ→ Config G c)(hj:(J: Filter ℕ)≤ atTop)(hs:Sweep K)(hx:Sweep H) : Steps (J:Filter ℕ) (fun n y=> c' n y (V n) m) (fun n y=> c'' n y (V n) m) :=by
     let f n:= (F₀ n).lotus (K n).tubes x χ o.K W o.a Q.table Q.halo (V n) m;let g n:= (F₁ n).lotus (H n).tubes x χ o.K W o.a Q.table Q.halo (V n) m
     have he n: HasDerivAt (fun y=> c' n y (V n) m) (f n) 0:=by unfold color; simpa only [one_mul] using (((hasDerivAt_id' (0:ℝ)).mul_const (f n)).const_add ((I n).spawn χ (V n) m))
     have hz n: HasDerivAt (fun y=> c'' n y (V n) m) (g n) 0:=by unfold color; simpa only [one_mul] using (((hasDerivAt_id' (0:ℝ)).mul_const (g n)).const_add ((T n).spawn χ (V n) m))
     refine ⟨fun i=> ⟨(he i).differentiableAt,(hz i).differentiableAt⟩,?_ ,?_⟩
     · refine (Draft.entryA I T R P' m V hs hx hM hj).carve (Eventually.of_forall fun n=> (congr_fun (color0 (F₀ n) (I n) χ (V n)) _).symm) (Eventually.of_forall fun n=> (congr_fun (color0 (F₁ n) (T n) χ (V n)) _).symm)
     simp_rw [fun i=> (he i).deriv,fun i=> (hz i).deriv]; exact lotusGlints I T R P' h hq hm hM hj m V
include hs hp
lemma roadJ : Jade X₀ X₁:=by
    refine ⟨tipJ I R h hs,tipJ T P' hq hp,fun p V J hj=>?_⟩
    have hL m:= colorJ I T R P' h hq hm hM m V hj hs hp
    rcases p with p|p; exact hL p.1
    let z:=(coefficient (I 0).seam p.2/ ((p.1+1).factorial:ℝ)); let F n t:= -z*∏ i,c' n t (V n) (p.2 i).val;let XH n t:= -z*∏ i,c'' n t (V n) (p.2 i).val
    have h: Steps (J:Filter ℕ) F XH:= (Steps.constJ _).multiplies (Steps.product Finset.univ (fun i=> hL (p.2 i).1)); refine ?_ -- equality Steps via pointwise.
    change Steps _ (fun n t=> - (I n).trainedMill (c' n t (V n)) p) (fun n t=> - (T n).trainedMill (c'' n t (V n)) p)
    convert h using 1; all_goals first | exact congr_arg _ rfl | skip
    · ext n t; unfold Cash.trainedMill Gas.term; change -((coefficient (I 0).seam p.2)* (∏ i,c' n t (V n) (p.2 i).val)/ _)=_; unfold F z; ring
    ext n t; unfold Cash.trainedMill Gas.term; change -((coefficient (I 0).seam p.2)* (∏ i,c'' n t (V n) (p.2 i).val) / _)=_; unfold XH z; ring
omit T P' hM hm hq hp
lemma omen: Back m₀:=by
    obtain ⟨u,hU,H⟩:= tipJ I R h hs|>.bins
    refine ⟨fun n (r:(I 0).Chainbook)=>manyW (u n) r ,hU.courtyard,fun n r V=>?_⟩ -- binder
    unfold Cash.smilesMill; split
    · let x:= X₀; let p(i:↥ r.fst):= r.2 i+1; let f (i:↥ r.fst) y:=x n y i.val V
      change priceJ (fun y=>manyW _ r) _; unfold manyW; apply carryJ; intro i
      have hx: |((p i).factorial:ℝ)⁻¹| = ((p i).factorial:ℝ)⁻¹:= abs_of_nonneg (by positivity)
      have h : (fun y=> f i y ^ p i / (p i).factorial)=fun y=> (((p i).factorial:ℝ)⁻¹)* f i y ^ p i:= funext fun i=> div_eq_inv_mul ..
      change priceJ (fun y=> f i y ^ p i / (p i).factorial) (u n i.val ^ p i / (p i).factorial); rw [h, div_eq_inv_mul]; have hp:= scaleJ (ascend (H n i.val V) (p i)) (((p i).factorial:ℝ)⁻¹); rw [hx] at hp; exact hp
    exact climbing price_zero (manyW_nonneg (hU.value n) _)
include T P' hm hM hp hq
lemma spinsJ : Jade m₀ m₁:=by
    refine ⟨omen I R h hs,omen T P' hq hp,fun i V J hj=>?_⟩
    let f (p:(I 0).Chapter)(n:ℕ)(y:ℝ):= X₀ n y p (V n); let g (p:(I 0).Chapter) n y:= X₁ n y p (V n)
    unfold Cash.smilesMill; let p(n):= (I n).Fresh i ∧ Ac.Spark (I n).bookFoot i.1 ∧ (I n).statesPool (V n) i; let A n y:=manyW (fun i=>f i n y) i; let B n y:=manyW (fun i=> g i n y) i
    have hh : Steps (J:Filter ℕ) A B:=by
        unfold A B manyW; simp_rw [div_eq_inv_mul]; exact Steps.product Finset.univ (fun j=> (Steps.constJ _).multiplies ((Jade.converge (roadJ I T R P' h hq hm hM hs hp) j.val V J hj).power _))
    convert Steps.switchJ hh p using 1
    · funext n y; by_cases ht:p n; swap; · rw [if_neg ht,if_neg (show ¬ (_ ∧ (_ ∧ _)) from ht)]
      rw [if_pos ht,if_pos (show _ ∧ _ ∧ _ from ht)]; rfl
    funext n y; by_cases ht:p n; swap; · rw [if_neg ht,if_neg (show ¬ ((T n).Fresh i ∧ Ac.Spark (T n).bookFoot i.1 ∧ (T n).statesPool (V n) i) from ht)]
    rw [if_pos ht,if_pos (show (T n).Fresh i ∧ Ac.Spark (T n).bookFoot i.1 ∧ (T n).statesPool (V n) i from ht)]; rfl

end Umbra
end YM.ConnectedActivityE6.Lim
