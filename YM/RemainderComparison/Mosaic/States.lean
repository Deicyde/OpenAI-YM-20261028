import YM.RemainderComparison.Mosaic.Shuttle

/-!
# Individual representatives on the eventual common coarse budget

Independent of Ω. Kernel/denominator derivative envelopes consumed elsewhere
(transport works with these integrated representatives on the output). Retain
all antecedents (libraries, roots) until RG03 Leaf attachment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Mosaic
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric
variable (N:Captain H j q d v u A b r B e n χ)
open Verse
local notation "B₀" => tile M H χ
local notation "E₀" => etude M H χ
local notation "A₀" => panel M H χ
local notation "L₀" => jewel M H χ
local notation "P₀" => parade M H χ

local notation "sx"=> radiusB x
variable (l:ι→ℝ)
open Mixed

def Shelter (S:StepData c f) (t:ℝ) (b : Support c)(f : Verse ι (Config G c)) : Prop:= Measurable f.utter∧ UsesFinal t b f.utter∧ GaugeInvariant f.utter ∧ ∀ i∈f.letters,∀ U, f.utter U≠0 → (M i).crest.image S.ratio.parent ⊆ b

lemma abode (p:Molecule S)(i:Drums M S): Shelter M S (Pressure.temp x) (H.unionP p) (B₀ p i):=by
   let M':= team M i
   obtain ⟨he,h,h'⟩:= M'.spinning T x χ H p; refine ⟨h',he,h,fun j hj V h s hp=> ?_⟩; exact mark_hit M H χ V s p i h j hj hp

include N
lemma model (p:H.Chapter)(w:Stone M H p): Shelter M S (Pressure.temp x) (H.bookFoot p) (A₀ p w):=by
   rcases p with p|p
   · exact abode M H χ ..
   let J:= A₀ (Sum.inr p) w; let c':= cadence H p; let X j:= B₀ (p.snd j).val (w j); let f V:=-(c' *∏ j,(X j).utter V)
   have ht : J.utter=f:= funext fun V=> congr_arg (- ·) (embarks M H χ N p w V)
   have hh j : Shelter M S (Pressure.temp x) (H.smallAt (p.snd j)) (X j) := abode M H χ ..
   change Shelter M S _ (reachability p) J; unfold Shelter; rw [ht]
   have hu i : H.smallAt (p.snd i)⊆ reachability p:= subset_biUnion_of_mem (H.smallAt ∘ p.snd) (mem_univ _)
   refine ⟨(measurable_const.mul (measurable_fun_prod _ fun i _=>(hh i).1)).neg,fun V U hζ hk=>?_,fun z U=> ?_,fun i hi U hL=>?_⟩
   · exact congr_arg (fun v:ℝ=> -(c'*v)) (prod_congr rfl fun i _=> inheritance (hh i|>.2.1) (hu i) V U hζ hk)
   · exact congr_arg (fun v:ℝ=> -(c'*v)) (prod_congr rfl fun i _=> (hh i|>.2.2.1) z U)
   obtain ⟨j,hj,hv⟩:= (holds (univ) (fun j=> (X j).letters) i).mp hi
   exact ((hh j|>.2.2.2) i hv U (fun h=> hL (by unfold f; rw [prod_eq_zero hj h,mul_zero,neg_zero]))).trans (hu j)
lemma landscape (p:H.Chainbook) (w:Scene M H p) : Shelter M S (Pressure.temp x) (H.library p) (P₀ p w):=by
   let a i j:= A₀ (i:↥p.fst).val (w i j); let c (V: Config G c) (i: ↥p.fst):= (∏ j,(a i j).utter V) / (↑((p.snd i+1).factorial):ℝ)
   let b (V: Config G _) := ∏ i,c V i
   let K(V : Config G _):= if sealing H p V then b V else 0
   let Q' := fun i:↥p.fst=> H.bookFoot i.val
   have hp i j:= model M H χ N (i:↥p.fst).val (w i j)
   have he (i:↥p.fst) : Q' i ⊆ H.library p:=subset_biUnion_of_mem H.bookFoot i.prop
   have ht : UsesFinal (Pressure.temp x) (H.library p) b:= fun V U hl hv=> Finset.prod_congr rfl fun i _=> congr_arg (·/_) (Finset.prod_congr rfl fun j _=> inheritance (hp i j|>.2.1) (he i) _ _ hl hv)
   have hk : GaugeInvariant b:=fun t V=> prod_congr rfl fun i _=> congr_arg (·/_) (prod_congr rfl fun j _=>(hp i j|>.2.2.1) t V)
   have hb : Measurable b:= measurable_fun_prod _ fun i _=> (measurable_fun_prod _ (fun j _=>(hp i j|>.1))).div_const _
   unfold Shelter; rw [show (P₀ p w).utter=K from rfl]
   refine ⟨?_,?_,?_,?_⟩
   · by_cases h:H.Fresh p∧ Ac.Spark H.bookFoot p.fst
     · refine Measurable.ite ?_ hb measurable_const; rw [show {V: Config G _| sealing H p V}=⋃ t∈ univ.filter (fun t=> H.inventory p.fst.toLeft=t∩H.library p),{V : Config G _|RG.flags (Pressure.temp x) V=t} from Set.ext (fun V: Config G _=> by simp [sealing,h.1,h.2,Cash.statesPool])]; exact MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=> RG.flags_measurable_eq ..
     rw [show K = fun _=>0 from funext fun V=> if_neg (show ¬sealing H p V from fun hx=>h ⟨hx.1,hx.2.1⟩)]; exact measurable_const
   · intro V U hl hs; have h : H.statesPool V p ↔ H.statesPool U p:= by unfold Cash.statesPool; rw [inter_comm, hs, inter_comm]
     simp_rw [K,sealing,h,ht V U hl hs]; split_ifs <;> rfl
   · intro t V; simp_rw [K,sealing,Cash.statesPool,gauge_flags,hk t V]; split_ifs <;> rfl
   intro i hi V hv
   unfold K at hv; split at hv; next hx=>
     obtain ⟨j,h,hj⟩:= (holds (univ) (fun j=>∑ l,(a j l).letters) i).mp hi
     obtain ⟨l,hl,h'⟩:= (holds univ (fun l=>(a j l).letters) i).mp hj
     refine ((hp j l|>.2.2.2) i h' V (fun hK=> hv (prod_eq_zero h ?_))).trans (he j)
     unfold c; rw [prod_eq_zero hl hK,zero_div]
   next=> exact False.elim (hv rfl)

-- Addresses from established enrollment output QB signs
open Progress.DirectedRecipe Mallow Ovens
variable {R':Rep G f} (Y:Cash W x μ L Q o C T R')(D:Match.Alliance Y H 1 0)(V:BudgetPoint)
variable (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hv: V.threshold=Pressure.temp x)
local notation "VB" => Refrain.read Y D χ E t'
variable (pK:Refrain.Leaf H)(w':Scene M H pK.val)
local notation "α₀" => pK.val
local notation "χ₀" => P₀ α₀ w'
local notation "ψ"=> Refrain.visa Y D pK
include hv
lemma pan : (VB).ForcedFamily V∧ Shelter M S V.threshold ((VB).forced ψ).support χ₀ ∧ ∀ U, (χ₀).utter U ≠ 0 → ((VB).forced ψ).eligible V.threshold U:=by
   have hp:= landscape M H χ N α₀ w'
   have hx:((VB).forced ψ).support= H.library α₀:= (Refrain.admitted Y D pK).1
   refine ⟨Refrain.qualified V Y D χ E t' hv,(by rw [hx,hv]; exact hp),fun U hn=>?_⟩
   rw [hv]; unfold ForcedAddress.eligible
   have ht: sealing H α₀ U:= Classical.byContradiction fun h=> hn (if_neg h)
   rw [hx,show ((VB).forced _).inventory=_ from (Refrain.admitted Y D pK).2, inter_comm]; refine ⟨ht.2.2.symm,?_⟩
   change Refrain.reserve Y (Refrain.badge Y ψ) |>.extraTest U; rw [Refrain.visited]; trivial
end YM.RemainderComparison.Mosaic
