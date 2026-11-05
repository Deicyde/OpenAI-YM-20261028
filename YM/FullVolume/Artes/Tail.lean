import YM.FullVolume.Antenna.Self
/-! Relational transcript and calibrations. Fixed forest tags.D.Period λ; acts across any histories, includes limit.Snow. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s:Sheet G}{L: Rolls s}(Q:PostCost L) (O:ChartRatio G)(m:ℕ)
structure Tale (a:Levels G)(m:ℕ) where
   input : PathData G
   stock : Flagship G
   receipts: PathData G
   sold : Flagship G
   Ψ: GainWire a m
   α:ℝ
-- choose ONE forest all by convention.Identity at limit.
def treeQ (a:Levels G)(m p:ℕ):Forest (a.clock.op m p).ratio:=Classical.choice (Tree.select _ (a.clock.op m p).patch.odd_side)
def keyQ (a:Levels G)(m p:ℕ):(a.clock.op m p).Choices:= Classical.arbitrary _
namespace Tale
variable {m} (T:Tale a m)
local notation "A"=> a.params (m+1)
local notation "R"=> a.params m
local notation "E"=> a.clock.J (m+1)
noncomputable def steaming :Words (a.S.side m) G :=fun i x=> thermal (treeQ a m i) (keyQ a m i) (A).clip T.input (T.Ψ i (treeQ a m i)) O (arm G _ 1 x)
noncomputable def ancient:Words (a.S.side m) G:=fun _=> inputSeries (R).clip T.receipts
noncomputable def traceN:Words (a.S.side m) G:= fun i=> turnSeries T.receipts.loop
noncomputable def pence:= T.α • T.ancient+T.traceN
noncomputable def prices: ConeRay.Section (a.S.side m) G:= tick _ (T.steaming O)-tick _ T.pence
-- relation holds only along true m lattice.Level.K.Data, keep raw Wave bound for limits
structure Earns (V:ℕ→Reel G) (J:FaceRow)(T:Tale a m) :Prop where
   arrives: Lash (V (m+1)) T.stock T.input
   goes : Lash (V m) T.sold T.receipts
   shape: Rig (V m) T.sold (a.S.side m) (R).paths (a.clock.loopCap m)
   bounds : haloB a (m+1) T.input
   out : T.receipts.Bounds (R).clip (R).width (R).paths (a.clock.loopCap m)
   average : Tender T.ancient (slots J G)
   salary x:alphaPay x (slots J G)=1
   score p (F: Forest (a.clock.op m p).ratio): PriceGap F (A).clip T.input (Q.η E) ∧
          Critical F (A).clip T.input (T.Ψ p F) ∧ ClassicalMatch F (A).clip (R).clip T.input T.receipts (T.Ψ p F)
   credit i:Toss (Q.Γ E*Real.exp (-Q.c E*(a.S.side m i).val)) ((T.prices O) i)

lemma merit (f:ℕ→Side) (p:Clip)(J:Bed)(σ vb A' Λ η Θ v M:ℝ)(S:PathData G)(hf:S.Bounds p vb A' Λ)(ht:0<σ)(hp: J.metric.strip σ v)(h:∀ i,Floor J p (f i) η Θ)(hy:∀ i,Bid.Sworn J (f i) G)(hs:Attached J S):
    Tender (fun i=>inputSeries p S (m:= f i)) (slots J.metric G)∧ ∀ x,alphaPay x (slots J.metric G)=1:=⟨⟨fun i=>(stain_knit _ _ hf|>.analytic),⟨_,_,ht,fun i j=> slots_cost ht hp i j⟩,fun i=>according (Row.rights _ _ hp ht.le) (low_columns hf hs (h i) (hy i)).2.2⟩,fun x=> by rw [alphaPay,tip_fuel x hp ht (h 0).starts]; norm_num⟩
lemma generous {i:ℕ}{n:ℕ}(J:Horizon a){T:Tale a m}(U:Bubble J Q O n m T.input T.receipts T.α T.Ψ)(p q: Site (a.S.side m i)) (x y:Twist G)(hx:∀ i j,‖x i j‖≤1)(hy:∀ i j,‖y i j‖≤1) : |T.prices O i ![pew p x,pew q y]|≤ cents (a.S.side m i) * (Q.Γ E*Real.exp (-Q.c E*(a.S.side m i).val)) :=by
   let c:=a.S.side m i; let f:= treeQ a m i; let S:=keyQ a m i; obtain ⟨h1,h2,h3,h4,h5⟩:= U.steps i f; let u:= thermal f S (A).clip T.input (T.Ψ i f) O; let v:= draft T.α T.receipts (R).clip (c:=c)
   have hp : ContDiffAt ℝ ω (u ∘ arm G c 1) 0:= (show ContDiffAt ℝ ω u ((arm G c 1) 0) from (arm G c 1).map_zero.symm ▸ h5.born S).comp _ (arm G c 1).contDiff.contDiffAt
   have ht: ContDiffAt ℝ ω (v ∘ arm G c 1) 0:= (show ContDiffAt ℝ ω v ((arm G c 1) 0) from (arm G c 1).map_zero.symm ▸ h5.classicalResult).comp _ (arm G c 1).contDiff.contDiffAt
   have hh:= h5.wave_price S p q x y hx hy; change |iteratedFDeriv ℝ 2 u 0 ![wave p x,wave q y] - iteratedFDeriv ℝ 2 v 0 ![wave p x,wave q y]| ≤ _ at hh; rw [wired_wave hp,wired_wave ht, mul_one,mul_assoc] at hh; exact hh
variable {Q T O}
lemma fromE {i:ℕ}{X:MapPrices}{J:Horizon a}{W:ℕ→Reel G}(U:Bubble J Q O i m T.input T.receipts T.α T.Ψ)(h:J.Suffices X)(hw:∀ k,Bid.Sworn (J.H i m) (a.S.side m k) G)(hm: m < i)(he:Lash (W (m+1)) T.stock T.input)(ht:Lash (W m) T.sold T.receipts)(hp:Rig (W m) T.sold (a.S.side m) (R).paths (a.clock.loopCap m))(hT:haloB a (m+1) T.input): T.Earns Q O W (J.H i m).metric := by
    obtain ⟨Ah,Z⟩:= merit _ _ _ _ _ _ _ _ _ _ 0 _ U.lives.bound (X.alpha_pos _) ((h.rows _ _ hm.le).2.1) (fun k=>h.all i m hm.le (a.S.side m k)) hw U.lives.ties
    refine ⟨he,ht,hp,hT,U.lives.bound,Ah,Z,fun i K=> let H:=U.steps i K; ⟨H.1,H.2.1,H.2.2.2.1⟩,fun i p q x y hx hy=> generous Q O J U p q _ _ hx hy⟩
lemma Earns.highly {J: FaceRow}{V:ℕ→Reel G}(U:T.Earns Q O V J): High (a.S.side m) (T.prices O):=
    ⟨_,fun i=> mul_nonneg (Q.pos _).le (Real.exp_pos _).le, mesh_tend _ (bound_climb G a m) (Q.posC _), U.credit⟩
end Tale
end YM.Stationary.Artes
