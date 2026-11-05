import YM.Extension.UV.Station.ProfileLimiter
import YM.Extension.UV.Station.Value
import YM.Extension.UV.Station.StepBill
import YM.Extra.WILSON_STARTUP.TopStep
/-! Passing the genuine classical matching equations to profile-array limits at every
fixed side. Readings concern **unmasked** germs; the nonperturbative activity equations
are not asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Extension.UV.StationaryData
open Filter Lattice Wilson RG Precision Exterior Bloch WilsonStartup.Change Tree
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {t q c d:Side} {S:StepData c d} (B:Forest S.ratio)
local notation "Maps"=> fieldDir G c 1
local notation "Z"=> AxisChart G B
local notation "V"=> Maps × Z
structure Flutter (p:Clip) (R:ℕ→PathData G) (P:PathData G) (t:Side) : Prop where
  bound_var : ∀ᶠ n:ℕ in atTop,∃ σ C Λ :ℝ,(R n).Bounds p σ C Λ
  bound_root : ∃ σ C Λ :ℝ,P.Bounds p σ C Λ
  reading {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E → Config G t)(hU:U 0=1)(h:∀ i,ContDiffAt ℝ ω (fun x=>G.mat (U x i)) 0): Tracks ∞ (fun n=> mainTerm p (R n) ∘ U) (mainTerm p P ∘ U) 0

structure Crossover (p p':Clip)(P Q:PathData G)(price:ℝ)(B:Forest S.ratio) : Type where
  choice : fieldDir G c 1→AxisChart G B

structure Crossover.Accepts {P Q:PathData G}{p p':Clip}{η:ℝ} (a:Crossover p p' P Q η B) (f:ℕ→Maps→Z) : Prop where
  positive : 0<η
  gap : PriceGap B p P η
  crit : Critical B p P a.choice
  result t : Matches 4 (onSlice B t p P ∘ graph a.choice) (mainTerm p' Q ∘ represent) 0
  travel k v : Tendsto (fun n=>dirT (f n) k 0 v) atTop (nhds (dirT a.choice k 0 v))

variable {p p':Clip} {P Q:PathData G}

def noise (θ:S.Choices) (z:V) := noiseTaylor S (represent z.1) (readFine B z) θ
lemma smooth_on (θ:S.Choices) (P:PathData G) (h:P.Bounds p 1 1 1) : True:=trivial
lemma lift_budget (P:PathData G) {p:Clip} (h : ∃ σ C Λ,P.Bounds p σ C Λ): ContDiffAt ℝ ω (mainTerm p P ∘ (readFine (G:=G) B)) 0:=by
 obtain ⟨σ,C,Λ,h⟩:=h; exact Work.F02.mainTerm_contDiffAt h (readFine_diff _)
lemma rep_budget (P:PathData G) {p:Clip} (h : ∃ σ C Λ,P.Bounds p σ C Λ): ContDiffAt ℝ ω (mainTerm p P ∘ (represent (n:=c))) 0:=by
 obtain ⟨σ,C,Λ,h⟩:=h; exact Work.F02.mainTerm_contDiffAt h fun i=>(Work.F03.represent_smooth _).contDiffAt
lemma noise_budget (θ:S.Choices) (T:PathData G) (f) (hf:Critical B p T f) (hv : ∃ σ C Λ,T.Bounds p σ C Λ) : ContDiffAt ℝ ω (noise (G:=G) B θ) 0:=
  (hf.2.2 θ).1.sub (lift_budget B T hv) |>.congr_of_eventuallyEq (Eventually.of_forall (fun _=> (add_sub_cancel_left ..).symm))

lemma solved_comp {E X F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup F][NormedSpace ℝ F]
  (p:ℕ→X→F)(q:X→F) (h:Tracks ∞ p q (0:X)) (g:ℕ→E→X) (L:E→X) (he:∀ᶠ n in atTop,g n 0=0 ∧ ContDiffAt ℝ ∞ (g n) 0)(hL:L 0=0)(hL':ContDiffAt ℝ ∞ L 0)
  (hw:∀ j w, Tendsto (fun n=>dirT (g n) j 0 w) atTop (nhds (dirT L j 0 w))) :
   ∀ k w,Tendsto (fun n=>dirT (p n ∘g n) k 0 w) atTop (nhds (dirT (q ∘ L) k 0 w)):=by
 intro k w
 let s : Finset (OrderedFinpartition k) := Finset.univ
 rw [pipeline q L _ (by exact hL.symm ▸ h.at_limit) hL']
 apply (partial_tends s g p L q w (r:=k) (fun a _ i=> a.partSize_le i) (fun a _ => a.length_le) ((he).mono fun n hi=>hi.1.trans hL.symm) (fun _ _=>hw _ _) (hL.symm ▸ h)).congr'
 filter_upwards [he,h.at_each] with n ⟨hz,hi⟩ hp
 exact (pipeline (p n) (g n) 0 (hz.symm ▸ hp) hi k w).symm

lemma cross_fly {R R':ℕ→PathData G} {f:ℕ→Maps→Z} (h:Flutter p R P d) (h':Flutter p' R' Q c) (η:ℝ) (hp:0<η)
 (hb:Bid.Larger (G:=G) S) (hc:∀ᶠ n:ℕ in atTop, Critical B p (R n) (f n) ∧ PriceGap B p (R n) η ∧ ClassicalMatch B p p' (R n) (R' n) (f n)) :
   ∃ a:Crossover p p' P Q η B,Crossover.Accepts B a f := by
 let H (θ:S.Choices)(P:PathData G): Profile Maps Z:=onSlice B θ p P
 have hn θ : ContDiffAt ℝ ω (noise (G:=G) B θ) 0 := by obtain ⟨n,⟨hf,-⟩,hR⟩ := (hc.and h.bound_var).exists; exact noise_budget B θ _ _ hf hR
 have hP θ : ContDiffAt ℝ ω (H θ P) 0:= (lift_budget B P h.bound_root).add (hn θ)
 have ht θ : Tracks ∞ (fun n=>H θ (R n)) (H θ P) 0:= (h.reading (E:=V) (readFine (G:=G) B) (readFine_one _) (readFine_diff _)).add (Tracks.unswerving _ ((hn θ).of_le le_top))
 have hPr : PriceGap B p P η:=by
    intro θ v; let w : Z→V:= fun x=>(0,x)
    have he:= (Tracks.unswerving w (contDiffAt_const.prodMk contDiffAt_id)|>.comply (ht θ) (Eventually.of_forall fun _=>rfl)).jet 2 (by exact WithTop.coe_le_coe.mpr (le_top (a:=(2:ENat))))
    have h₀ : (H θ P ∘ w)=tested B θ p P 0:=rfl
    exact ge_of_tendsto (mapply (h₀ ▸ he) (tendsto_const_nhds (x:=![v,v]))) (hc.mono fun n hh=> hh.2.1 θ v)
 have hz θ : vert (H θ P) (0:V)=0:= by
    have hy n (hn:Critical B p (R n) (f n)) := station_of hn θ
    have h₁ n (hn:Critical B p (R n) (f n)): (vert (H θ (R n))) 0=0:= by
      have hs: vert (H θ (R n)) (graph (f n) 0)=0:= (hy n hn).law.self_of_nhds
      rw [(hy n hn).at0] at hs; exact hs
    have hq n : graph (f n) 0 = ((0:Maps), f n 0) := rfl
    have h₂:= (ht θ).vertical.evaluated
    exact tendsto_nhds_unique h₂ (Filter.EventuallyEq.tendsto (hc.mono fun n hn=>h₁ n hn.1))
 obtain ⟨g,hg⟩:=new_crit hb.1 (fun θ=>hP θ) hPr hp hz
 have hy θ := definite_of hPr hp θ (hP θ); let θ0:= (Classical.arbitrary S.Choices)
 have hL:= solved f g (ht θ0) (hc.mono fun n hn=> (hn.1.2.2 θ0).1) (hP θ0) (hc.mono fun n hn=>station_of hn.1 θ0) (station_of hg θ0) (hc.mono fun n hn=> (definite_of hn.2.1 hp θ0 (hn.1.2.2 θ0).1 |>.forms)) (hy θ0).forms
 refine ⟨⟨g⟩,hp,hPr,hg,fun θ=>?_,hL⟩
 have hA : ContDiffAt ℝ ω (H θ P ∘ graph g) 0:= (((station_of hg θ).at0.symm ▸ hP θ).comp _ (station_of hg θ).chart)
 have hB : ContDiffAt ℝ ω (mainTerm p' Q ∘ (represent (n:=c))) 0:= rep_budget Q h'.bound_root
 refine ⟨hA,hB,fun k hk=> dirT_ext hA hB fun v=>?_⟩
 let u:=fun n=> graph (f n)
 have he n j (hn:Critical B p (R n) (f n)): dirT (u n) j 0 v=(dirT (id:Maps→Maps) j 0 v,dirT (f n) j 0 v):=tensor_joint (H θ P) _ _ 0 contDiffAt_id (hn.2.1.of_le le_top) v
 have he' := fun j=>tensor_joint (H θ P) id g 0 contDiffAt_id (hg.2.1.of_le le_top) (k:=j) v
 have hU j w : Tendsto (fun n=>dirT (u n) j 0 w) atTop (nhds (dirT (graph g) j 0 w)):=by
    change Tendsto _ _ (nhds (dirT (fun z=>(id z,g z)) j 0 w)); rw [tensor_joint (H θ P) id g 0 contDiffAt_id (hg.2.1.of_le le_top)]
    apply (tendsto_const_nhds.prodMk_nhds <| hL j w).congr'
    filter_upwards [hc] with n hn
    exact (tensor_joint (H θ P) _ _ 0 contDiffAt_id (hn.1.2.1.of_le le_top) w).symm -- infer graph?
 let a n:=mainTerm p' (R' n) ∘ (represent (n:=c))
 have h₀ : Tendsto (fun n=>dirT (a n) k 0 v) atTop (nhds (dirT (H θ P ∘ graph g) k 0 v)):=by
    apply (solved_comp (E:=Maps) _ _ (ht θ) u (graph g) ?_ ((station_of hg θ).at0) ((station_of hg θ).chart.of_le le_top) hU k v).congr'
    · exact hc.mono (fun n hn=>DFunLike.congr_fun (hn.2.2 _ hk θ).2.2 (fun _:Fin k=>v))
    · filter_upwards [hc] with n hn; exact ⟨(station_of hn.1 θ).at0, (station_of hn.1 θ).chart.of_le le_top⟩
 exact tendsto_nhds_unique h₀ (tracks_t (x:=0) _ _ (h'.reading _ link_one (fun i=>(Work.F03.represent_smooth _).contDiffAt)) k v)
#print axioms cross_fly
end YM.Extension.UV.StationaryData
