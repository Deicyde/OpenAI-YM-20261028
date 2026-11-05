import YM.UVExtension.Bud.Crook
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε : ℝ}
local notation "R₁" => A.B.a.budget (m+1)
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
local notation "Pv" => mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
variable (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)

variable (T:Levels G)(j k:ℕ)(U:Cham T j k)(v:Valve j k T U)
local notation "P0"=> T.budget j
local notation "Ft"=> (Tabernacle.floor P0 v.val)
local notation "St"=> T.S.side j k
set_option quotPrecheck false
lemma turnsP0 (s: Signed)(b:Site St) : Surjective (pull s b : Config G St → Config G St) :=fun X=>by
   refine ⟨pull s⁻¹ (-((s⁻¹).act b)) X,?_⟩; rw [pull_pull,show Lattice.affine s⁻¹ _ b=(0:Site St) from (by simp [Lattice.affine]), inv_mul_cancel,pull_one]; funext e; simp [Lattice.translate]
def darkE (i:ℕ):Prop:=∀ v:Vase T j k U,v.val.val.1 i=0
def darkK (i:ℕ):Prop:=∀ v:Vase T j k U,v.val.val.2 i=0
private lemma bondsA {A Z : Type} [Zero Z] (f g:A→ Z) (L:A → A) (he:Surjective L)(h:g=f ∘ L): f=0 ↔ g=0:=by
   constructor; · intro he; rw [h,he]; rfl
   intro hv; funext i; obtain ⟨j,rfl⟩:= he i; exact congr_fun (h.symm.trans hv) j
variable (s:Signed) (b:Site (T.S.side j k))
local notation "R!"=> U.maps P0 v s b
lemma walksE (i:ℕ): darkE T j k U i ↔ darkE T j k U ((R!).ep i):=by
   apply forall_congr'; intro y; let v':=y.val; have hh : (R!).ep=(U.maps P0 v' s b).ep:= (U.choice P0 v s b|>.1).trans ((U.choice P0 v' s b).1.symm); rw [hh]
   exact bondsA _ _ _ (turnsP0 T _ _ _ _) (funext (fun z=> (U.maps P0 v' s b).valuesE i z))
lemma walksK (i:ℕ): darkK T j k U i ↔ darkK T j k U ((R!).kp i):=by
   apply forall_congr'; intro y; let v':=y.val; have hh : (R!).kp=(U.maps P0 v' s b).kp:= (U.choice P0 v s b|>.2).trans ((U.choice P0 v' s b).2.symm); rw [hh]
   exact bondsA _ _ _ (turnsP0 T _ _ _ _) (funext (fun z=> (U.maps P0 v' s b).valuesK i z))
noncomputable def mute : Sheath T j k:= (fun i=>if darkE T j k U i then 0 else v.val.1 i,fun i=>if darkK T j k U i then 0 else v.val.2 i)
local notation "U'"=> Tabernacle.floor P0 (mute T j k U v)
lemma outMoves : ∃ F:(U').Moves s b,Twins F (U.run s b):=by
    let F:= R!; refine ⟨⟨F.ep,F.kp,F.reg_site,F.reg_support,F.forced_support,F.forced_inventory,F.forced_tests,fun i W=>?_,fun i W=>?_⟩, U.choice P0 v s b⟩
    · change (mute T j k U v).1 (F.ep i) W=(mute T j k U v).1 i (pull s b W); unfold mute; dsimp only; simp_rw [← show darkE T j k U i ↔darkE T j k U (F.ep i) from walksE T j k U v s b i]; split; rfl; exact F.valuesE i W
    change (mute T j k U v).2 (F.kp i) W=(mute T j k U v).2 i (pull s b W); unfold mute; dsimp only; simp_rw [← show darkK T j k U i ↔darkK T j k U (F.kp i) from walksK T j k U v s b i]; split; rfl; exact F.valuesK i W
private lemma portable {σ α:ℝ}(hv: Activities.Valid Ft P0 σ α) : Activities.Valid (U') P0 σ α:=by
   obtain ⟨q,r,hE,hK,hY⟩:=hv
   have ht: ((Tabernacle.floor P0 (0:Sheath T j k))).RegularFamily P0:=by
      let z:Valve j k T U:=0; obtain ⟨b,c,h⟩:= U.income P0 z|>.1; exact h.regular
   refine ⟨⟨fun i=>?_,fun i=>?_,fun i=>?_⟩,⟨fun i=>?_,r.symtest,fun i=> ?_,r.meas_test,fun i=>?_,r.reads_test,fun i W h=>?_⟩,fun s b=>⟨(outMoves ..).choose⟩,?_,?_⟩
   all_goals unfold Tabernacle.floor mute; dsimp only <;> try split
   · exact ht.smooth _
   · exact q.smooth _
   · rfl
   · exact q.at_flat _
   · exact ht.vanish i
   · exact q.vanish i
   · exact fun _ _=>rfl
   · exact r.sym _
   · exact measurable_const
   · exact r.meas _
   · exact fun _ _ _ _=>rfl
   · exact r.reads _
   · -- permit after not unfold
     unfold mute Tabernacle.floor at h; dsimp only at h
     split at h; next => exact (h rfl).elim
     next=> exact r.permit i W h
   · obtain ⟨f,hf,hQ⟩:=hK; refine ⟨f,fun i=>?_,hQ⟩; dsimp only; split; swap; · exact hf _
     exact VerifiedReset.sup_le (CouplingShape.sup_const (G:=G) 0) (abs_zero.trans_le (hf i).1)
   obtain ⟨f,hf,hQ⟩:=hY; refine ⟨f,fun i=> ⟨(hf i).1,fun u=>?_⟩,hQ⟩; dsimp only; split; next h=> exact norm_zero.trans_le (hf i).1
   exact (hf i).2 _

lemma susceptible : Tabernacle.copied P0 U (mute T j k U v):=by
    obtain ⟨x,K',H⟩:= (U.income P0 v).1; exact ⟨⟨x,K',portable _ _ _ _ _ H⟩,fun s b=> outMoves T j k U v s b⟩
def humor : Valve j k T U:=⟨_,susceptible T j k U v⟩
abbrev sleepy : Vase T j k U:= ⟨humor T j k U v, by
   refine ⟨rfl,rfl,fun i=> if_pos (show darkE T j k U (blankRow St i) from fun x=> ((show HasSlots .. from x.property).regular i)),fun i=> if_pos (show darkK T j k U (sleepK G St i) from fun x=> ((show HasSlots .. from x.property).forced_zero i))⟩⟩
lemma tipping (h : HasSlots P0 Ft): (sleepy T j k U v).val=v:=by
   let X:Vase T j k U:=⟨v,h⟩; apply Subtype.ext; refine Prod.ext ?_ ?_
   · funext i V; change (mute T j k U v).1 i V=_; unfold mute; dsimp only; split; next h=> exact (congr_fun (h X) V).symm
     rfl
   funext i V; change (mute T j k U v).2 i V=_; unfold mute; dsimp only; split; next h=> exact (congr_fun (h X) V).symm
   rfl
lemma costP (h:‖place T j k U v‖≤1): ‖place T j k U (sleepy T j k U v).val‖≤1:= (tapT _ _ _ _ _).2 (portable _ _ _ _ v ((tapT _ _ _ _ v).1 h))

def willow : Valve j k T U→ₗ[ℝ] Vase T j k U where
    toFun := sleepy T j k U
    map_add' x y:=by
       apply Subtype.ext; apply Subtype.ext; change mute T j k U (x+y)= mute T j k U x+mute T j k U y; unfold mute; refine Prod.ext ?_ ?_
       all_goals funext i V; dsimp; split <;> simp
    map_smul' a x:=by
       apply Subtype.ext; apply Subtype.ext; change mute T j k U (a • x)=a • mute T j k U x; unfold mute; refine Prod.ext ?_ ?_
       all_goals funext i V; dsimp; split <;> simp
end YM.UVExtension.Dales
