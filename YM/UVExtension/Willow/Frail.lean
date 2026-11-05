import YM.UVExtension.Willow.Cloud
import YM.UVExtension.Copse.Scent
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Willow
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable (K : Festa Q L H V b B) (hx:X.x=x) (hX : X.width=o.K) (hm:X.manifest)
    (p : Molecule S) (M:Lotus.Leaf R) (hl:Lines R V b (betaF G x L) M) -- using PhysicalNext.Repeat to open
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => grains X R W o.a Q.table Q.halo V M p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
open Daisy Daisy.Charity March Ursell Trees Greenbelt Concert Refrain
variable {q' : Q.rate≤γ} {h':γ<0} {l t r d:ℝ}
variable (Y:Pavilion H V B γ v l q' h') (hY : Pouch G L x l)(hR:0 ≤ Q.exp-l)
local notation "ι'"=> radiusB x
local notation "Yt"=> ((stalk Q q' h').costs L μ)
local notation "m'"=> M.turn.badge S
variable (k:ℕ)
-- all addresses agree across origin H.Frame. cols.
variable (χ:Chi) (J : (d:Canvas (betaF G x L) b ι)→ Cash W x μ L Q o a T (freshen d R V)) (U:Config G c)
local notation "Tπ"=> aperture K
local notation "tD"=> Canvas (betaF G x L) b ι
include Y hl K hY hR
lemma falls (i:Molecule S): Bumps (Tπ).span (fun z=>mist (H:=H) (V:=V) M χ U z i):=by
   intro U f hS hp hh; apply (DifferentiableOn.const_mul); exact (DifferentiableOn.fun_sum (fun j (_:j∈Finset.univ)=> bud _ K rfl rfl i M hl Y hY hR U f hS hp hh))
variable (z:Vines ι)(hz:z∈parade (betaF G x L) B)
include hz
omit hR in
lemma stay :∃ v:Molecule S→ℝ, SumBudget (fun i=> v i*Copse.worth k (radiusB x) (Q.exp-l) (H.unionP i)) (ceiling (H:=H) k M) ∧ ∀ i U, ‖mist (H:=H) (V:=V) M χ U z i‖ ≤ v i:=by
   letI:Nonempty (Tree.Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
   obtain ⟨J,⟨N⟩⟩:= Y.build z hz; refine ⟨_,heights M k N,fun i U=>?_⟩
   unfold mist; rw [norm_mul,norm_inv,Complex.norm_natCast]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun j _=> bough (prism T x χ o.K U (allot j)) K rfl rfl i M hl hY k hz N))) (by positivity)).trans_eq ?_; rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ (by positivity)]

-- hol derivative pair engagements use BOTH value and brush. This file value only.
local notation "Tr"=> fun i: H.fragrances=> H.bookFoot (.inr i)
omit hz
variable (p0:H.fragrances)
abbrev plume (d:tD) := puff (H:=H) (cant χ J U d ∘ Subtype.val) (fun i=> rateA (Q:=Q) (o:=o) (T:=T) M hl χ U i.val d) p0
def plumes (z:Vines ι) :=(coefficient H.seam p0.2:ℂ) *((p0.1+1).factorial:ℂ)⁻¹*∑ i:Option (Fin p0.1),(∏ j∈univ.erase i, grain U χ H V (p0.2 j).val z)*mist (H:=H) (V:=V) M χ U z (p0.2 i).val
omit Y hY hR in
lemma gazeV (d:tD): plumes (H:=H) (V:=V) M χ U p0 ((Tπ).call d)=↑(plume M hl χ J U p0 d):=by
   unfold plumes plume puff; push_cast
   apply congr_arg; refine Finset.sum_congr rfl fun i _=> ?_; apply congr_arg₂ (·*·) _ (reads K M hl χ U d _); exact prod_congr rfl fun j _=> grainR J U χ K d _
lemma pipes : Bumps (Tπ).span (plumes (H:=H) (V:=V) M χ U p0):=by
    intro S T h hp hh; exact (DifferentiableOn.fun_sum (fun i (_:i∈Finset.univ)=> (DifferentiableOn.fun_finsetProd (fun j _ => grainL K Y hR U χ (p0.2 j).val (p0.2 j).2.1 S T h hp hh)).mul (falls K M hl Y hY hR χ U (p0.2 i).val S T h hp hh))).const_mul _
omit hl Y K hY hR
lemma pricedV {f':H.ThinP→ℝ} {u':H.ThinP→ℝ} (hf:∀ i,‖grain U χ H V i.val z‖≤ f' i)(hu:∀ i,‖mist (H:=H) (V:=V) M χ U z i.val‖ ≤ u' i) : ‖plumes (H:=H) (V:=V) M χ U p0 z‖≤ Copse.center H.seam f' u' p0.2:=by
    unfold plumes; rw [norm_mul,norm_mul,norm_inv,Complex.norm_natCast, Complex.norm_real,Real.norm_eq_abs,Copse.tends]; refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=>?_)) (by positivity); rw [norm_mul,norm_prod]; exact mul_le_mul (prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hf _)) (hu _) (norm_nonneg _) (Finset.prod_nonneg fun _ _=> (norm_nonneg _).trans (hf _))
include Y K hl hY
variable {A B' :ℝ}(hA:0≤A)(hb:0 < B')(hp:A+B' ≤ Q.exp-l)
local notation "Jp"=> (stalk Q q' h')
variable (hB:degreePrice (radiusB x) ((stalk Q q' h').overture L μ x 0) B'≤1/2)
include hB hp hb hA
-- preserve same order d map output
lemma blush (z:Vines ι)(hz:z∈parade (betaF G x L) B): Meter.MeasureP (Copse.nose (G:=G) (Tr) k (radiusB x) A) (fun i U=> plumes (H:=H) (V:=V) M χ U i z) (ceiling (H:=H) k M*(1-1/2)⁻¹):=by
   obtain ⟨f,g,h,hg,hf,hgF,he⟩:= grip K Y χ z hz hp
   obtain ⟨u,hu,hA'⟩:= stay K M hl Y hY k χ z hz
   have ht': Ready H.smallAt (radiusB x) f A ((Jp).overture L μ x 0) B' (1/2):=⟨(stalk Q q' h').overture_pos x 0 (Festa.altitude (H:=H)),hb,hB,by norm_num,hf,h⟩
   let v': H.ThinP→ℝ:= u ∘ Subtype.val
   have hv':∀ i,0≤ v' i:=fun i=>(norm_nonneg _).trans (hA' _ 1)
   apply (Copse.rests k _).2
   refine ⟨_,Copse.tangled _ _ _ _ H.testS ht' hA hv' ?_,fun i U=>pricedV (V:=V) M χ U z i ?_ ?_⟩ -- goals
   · refine budget_mono (budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective hu) ?_ ?_
     · exact fun i=>mul_nonneg (hv' _) (Real.exp_pos _).le
     exact fun i=>mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (hv' i)
   all_goals first| exact (he U).1| exact fun i=>hA' i.val U
lemma rasps : Nonempty (Atlas (Copse.nose (G:=G) Tr k (radiusB x) A) (Tπ) (fun d i U=> plume M hl χ J U i d) (fun _=> ceiling (H:=H) k M * (1-1/2)⁻¹)):= by
   refine ⟨⟨fun z i U=> plumes (H:=H) (V:=V) M χ U i z,fun d i U=> gazeV K M hl χ J U i d,fun i U=> pipes K M hl Y hY (by linarith) χ U i,fun z hz=>?_⟩⟩
   exact blush K M hl Y hY k χ hA hb hp hB z hz
end YM.UVExtension.Willow
