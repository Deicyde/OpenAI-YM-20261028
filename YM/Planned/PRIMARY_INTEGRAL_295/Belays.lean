import YM.Planned.PRIMARY_INTEGRAL_295.Breen
import YM.Planned.PRIMARY_INTEGRAL_295.Moulin
/-!
# Unscaled F0 coupons on K genuine sums

Purchase before path with only fixed L.RP primitive. Using unforced chart
form before conditional masks.Album and requires exact linking from actual
history separately later. K World.Funds & Branch. Analytical through any
n including zero at true positions including s flags of Keys. Equality H.FIELD
Book separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Belays
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {k n d:ℕ} {c f : Side} {S:StepData c f}

-- `Xf,R,V` universal for any ticket with U chart allowance prezed.
lemma Xcost (G:Gauge)(k:ℕ)(p:Stage)(C:ℝ)(hc:0≤C):∃ B:ℝ,1≤B∧
   ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{c:Side}{U:E→Config G c}{x:E}(R:PathData G)
    (_:∃ Λ,R.Bounds p.clip p.width p.paths Λ)(_ :∀ i,Allows k (fun y=>G.mat (U y i)) x C)
     (L d:ℕ)(_ :0<d)(j:Twin c), Allows k (fun y=>Pressure.plotted R p.clip L d (U y) j) x B:=by
   obtain ⟨B,hB,hT⟩:= Drupes.shot C hc G k p.clip
   obtain ⟨A,hA,hp⟩:= measured C hc G k p.width p.width_pos
   refine ⟨max B (A*p.paths),hB.trans (le_max_left ..),?_⟩; intro E _ _ c U x P ⟨Λ,h⟩ hU L d hd ⟨j,i⟩
   cases i
   · exact (hT hU _).mono (le_max_left ..)
   let D:=garth d L; let f (s : Slot) :=fun y:E=>s.atSite (U y) j.1; let r (s:Slot):= chip P j.2 s
   have hg (s:Slot): Allows k (fun x=>r s • f s x) x (|r s| * (A*Real.exp (p.width*s.length))):= (hp hU hU j.1 s).smul _
   have hb:= Push.Uniform.allows_sum (s:=D) (fun s _ => hg s)
   have hh : (∑ s∈D,|r s| * (A*Real.exp (p.width*s.length))) ≤ A*p.paths:=by
      have hx s: |r s| * (A*Real.exp (p.width*s.length))= A*(|r s| * Real.exp (p.width*s.length)):=by ring
      simp_rw [hx,←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Price.cooked P h j.2 d L) (by linarith)
   change Allows k (fun y=>shorten P L d (U y) j) x _
   simp_rw [Festoons.clipped_short P h j _ L d hd]; exact (hb.mono hh).mono (le_max_right ..)

lemma mixed_1 (G:Gauge)(n:ℕ):∃ C:ℝ,1≤C∧ ‖(1:G.Mat)‖ ≤ C ∧ ∀ c (s:Signed) (x:Dir G c), ‖x‖≤1→ ∀ i, Allows n (fun y=> G.mat (venue s y i)) x C:= by
    obtain ⟨K,hK,h⟩:= exists_allows (s:=closedBall (0:G.Color) 1) (isCompact_closedBall _ _) (fun i _=>G.exp_jet.contDiffAt (x:=i)) n
    let C:=max K (max 1 ‖(1:G.Mat)‖)
    refine ⟨C,(le_max_left ..).trans (le_max_right ..),(le_max_right (1:ℝ) ‖(1:G.Mat)‖).trans (le_max_right ..),fun c s x hx i=>?_⟩
    have hg (i:Bond c): Allows n (fun y:Dir G c=>G.mat (represent y i)) x K:=by
       let L:Dir G c→L[ℝ] G.Color:=ContinuousLinearMap.proj (φ:=fun _=>G.Color) (pole i)
       have hh:‖L‖ ≤ 1:= by apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv; exact (norm_le_pi_norm v _).trans hv.le
       simp_rw [Work.F03.represent_link]; exact pulse_left L (h _ (mem_closedBall.mpr (by rw [dist_zero_right]; exact (norm_le_pi_norm x (pole i)).trans hx))) hh
    let u:=sendEdge s 0 i
    unfold venue pull Lattice.Step.read
    split
    · exact ((hg u).inverse (f:=fun y : Dir G c=> represent y u)).mono (le_max_left ..)
    exact (hg u).mono (le_max_left ..)

-- portal into ERA.CALL service and bias kit.
structure SourceKit (K:Core G S) (n:ℕ)(v:Dir G c) (C:ℝ): Prop where
    ours (i:Bond f)(s:Signed):Allows n (fun x=> G.mat (K.seek s x 0 i)) v C
    turns (i:Bond c)(s:Signed):Allows n (fun x=> G.mat (venue s x i)) v C
    asks (i:Bond c)(s:Signed):Allows n (fun x=> G.mat (K.target s x 0 i)) v C

lemma days (G:Gauge)(n:ℕ)(P:Patch)(Q:KernelChoices):∃ r C:ℝ,1≤C∧ ‖(1:G.Mat)‖ ≤ C ∧ 0<r∧ r≤1∧ ∀ c f(S:StepData c f)(K:Core G S),S.kernel=Q→S.patch=P→∀ v,‖v‖ ≤ r→ SourceKit K n v C:=by
   obtain ⟨C,hC,hp,h⟩:=mixed_1 G n
   obtain ⟨A,hA,hB,H⟩:=winding G n
   obtain ⟨r,B,hr,hD,hv,he⟩:=binning G n Q P
   let D:=max C (max A B)
   refine ⟨r,D,hC.trans (le_max_left ..),hp.trans (le_max_left ..),hr,hv,fun c f S K hQ hP v ht=> ?_⟩
   let L:Dir G c→L[ℝ] Hollow G c f:=ContinuousLinearMap.inl ..
   have hL(v:Dir G c):‖L v‖≤‖v‖:=by change max ‖v‖ ‖(0:Temps G f)‖≤_; simp
   have hh:= (hL v).trans ht
   have hy:‖L‖ ≤ 1:=ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one (fun v hv=> (hL v).trans hv.le)
   exact ⟨fun i s=> (pulse_left L (f:=fun y=>G.mat (termook s K y i)) ((H c f S K s).2.2 i (L v) (hh.trans hv)) hy).mono ((le_max_left ..).trans (le_max_right ..)),
     fun i s=> (h c s v (ht.trans hv) i).mono (le_max_left ..),fun i s=> (pulse_left L (f:=fun y:(Hollow G c f)=>G.mat (K.target s y.1 y.2 i))
       (he c f S hQ hP K s i (L v) hh) hy).mono ((le_max_right A B).trans (le_max_right ..))⟩

private def mixer (G:Gauge): Pay G→L[ℝ] G.Color→L[ℝ] G.Color:= (ContinuousLinearMap.apply ℝ G.Color (E:=G.Color)).flip
section Boxes
variable (G:Gauge)(n:ℕ)(P:Patch)(Q:Teller G) (C:ℝ) (hC:0≤C)(h1:‖(1:G.Mat)‖≤C)
include hC h1

/-- Access for M v/w call; combined weight C. Useful also for exposing costs
later. Does not require M*H diagonal. -/
lemma territories :∃ M:ℝ,1≤M∧ ∀ c f(S:StepData c f)(K:Core G S),S.patch=P→ Teller.Funds Q S K.tube→∀ s (v:Dir G c),SourceKit K n v C →
      let a:=fun x:Dir G c=> venue s x; let X:=K.R; let M':=K.tube
      (∀ i:Twin f, ∃ c:Twin c→ℝ,(∑ j,c j)≤M ∧ ∀ j, Allows n (fun x=>M'.Φ X (a x) i j) v (c j)) ∧
      (∀ i:Bond c, ∃ c:Twin c→ℝ,(∑ j,c j)≤M ∧ ∀ j, Allows n (fun x=>M'.Φ' X (a x) i j) v (c j)):=by
   let D:= max (max 0 Q.C) (Q.C / (P.L.val:ℝ)^2)
   have hD: 0≤D:= (le_max_left ..).trans (le_max_left ..)
   obtain ⟨A,ha,h⟩:=Breen.pencils G n P Q.η C D Q.width hC hD
   obtain ⟨B,hb,hb'⟩:=Breen.resumes G n P Q.η C D Q.width hC hD
   refine ⟨max A B,ha.trans (le_max_left ..),fun c f S K hP hv s v hp=>?_⟩
   intro a X M'
   constructor
   · intro i
     have ht : M'.R.mf.strip Q.η D := by intro i j; obtain ⟨rfl⟩:=hP; exact (hv.crosses.2.2.1 i j).mono le_rfl (le_max_right ..)
     have hh(i): Allows n (fun x=> G.mat (replica S.ratio (a x) i)) v C:=by
       unfold replica; split
       · apply allows_const v; change ‖G.mat (1:G.El)‖≤_; rw [G.mat_one]; exact h1
       exact hp.turns _ s
     obtain ⟨m,hm,hM⟩:= hb' S K hP ht a i v hh; exact ⟨m,hm.trans (le_max_right ..),hM⟩
   intro i; obtain ⟨m,hm,hM⟩:= h S K hP (show M'.R.mn.strip Q.η D from fun i j=> (hv.crosses.1 i j).mono le_rfl ((le_max_right 0 Q.C).trans (le_max_left ..))) a i v (fun i=> hp.turns i s)
   exact ⟨m,hm.trans (le_max_left ..),hM⟩

omit hC h1 in
private lemma coffers {X : Type} [Fintype X] {I : X→ E→ Pay G} {J:E→X→G.Color} (x:E) {C M : ℝ} (h:∃ c:X→ℝ,
      (∑ i,c i)≤C ∧ ∀ i, Allows n (I i) x (c i)) (ht:0≤M) (hv :∀ i,Allows n (fun y=> J y i) x M): Allows n (fun y=>∑ i:X,I i y (J y i)) x
        (2^n*‖mixer G‖*C*M):=by
    obtain ⟨m,hm,hM⟩:=h
    have he:= Push.Uniform.allows_sum (s:=Finset.univ) (fun i (_:i∈Finset.univ)=> (hM i).bilinear (mixer G) (hv i) le_rfl)
    apply he.mono; rw [← Finset.sum_mul,← Finset.mul_sum]; gcongr

lemma wired : ∃ M:ℝ,1≤M∧∀ c f(S:StepData c f)(K:Core G S),S.patch=P→Teller.Funds Q S K.tube→∀ v:Dir G c,SourceKit K n v C →
    ∀ i:Seats G c f, Allows n (fun x=> K.F0 x i) v M:=by
   obtain ⟨A,hA,hS⟩:= territories G n P Q C hC h1
   obtain ⟨B,hB,h₂⟩:= Xcost G n Q.below C hC
   obtain ⟨X,hX,h₁⟩:= Xcost G n Q.top C hC
   let Z:= |Real.sqrt Q.bind.penalty| * (oneL G*(2^n*C*C)); let R:=2^n*‖mixer G‖*A*B
   have hr:0≤R:=by unfold R; positivity; -- trailing
   have hz:0≤Z:=by unfold Z; have h:=hOneL G; positivity
   let Y:=max Z X
   let M:= |ballast| * (Y+R); have hY:1≤ Y:=hX.trans (le_max_right ..)
   have hm:0≤M:=by unfold M; positivity
   refine ⟨1+M,by linarith,fun c f S K hk hv v ht ⟨⟨s,i⟩,j⟩=>?_⟩
   let U(x:Dir G c):= venue s x; let t:=K.tube; let a:=K.R; let V(x:Dir G c):=K.seek s x 0
   let J(x:Dir G c):= t.Xn a (U x)
   obtain ⟨D,D',hd,hD⟩:=hv.feeds
   have hx(i:Twin c): Allows n (fun x=> J x i) v B:= by
       unfold J Tube.Xn t; rw [hv.low]; exact h₂ K.tube.down ⟨_,hD⟩ (fun i=>ht.turns i s) _ _ S.patch.L.property i
   obtain ⟨hf,hp⟩:= hS c f S K hk hv s v ht
   have he: Allows n (fun y=> K.bind (s,i) y) v (Y+R):=by
     rcases i with p|p
     · let L(x:Dir G c):=Pressure.zip (t.Φ a (U x)) (J x) p
       have hg: Allows n L v R:= coffers G n v (hf p) (zero_le_one.trans hB) hx
       have he : Allows n (fun x=>t.Xf a (V x) p) v X:=by unfold t Tube.Xf; rw [hv.high]; exact h₁ K.tube.up ⟨_,hd⟩ (fun i=> ht.ours i s) _ _ one_pos p
       have hh:= (he.mono (le_max_right Z X)).add (hg.smul (-1))
       simp only [neg_smul,one_smul,abs_neg,abs_one, one_mul] at hh; simpa only [sub_eq_add_neg] using! (show Allows n (fun x=>t.Xf a (V x) p + - L x) v _ from hh)
     let L(x:Dir G c):=Pressure.zip (t.Φ' a (U x)) (J x) p
     have hg: Allows n L v R:= coffers G n v (hp p) (zero_le_one.trans hB) hx
     let v'(x:Dir G c):= K.target s x 0
     let F(x:Dir G c):= Pressure.Tube.Z S (v' x) (U x) p
     have he : Allows n F v Z:= by
        have he:= (ht.turns p s).times (f:=fun x=>U x p) ((ht.asks p s).inverse (f:=fun x=>v' x p))
        unfold F Tube.Z; simp_rw [identifies]; rw [hv.knobs]; exact (he.linear (cbr G) le_rfl).smul _
     have hh:= (he.mono (le_max_left Z X)).add (hg.smul (-1))
     simp only [neg_smul,one_smul,abs_neg,abs_one, one_mul] at hh; simpa only [sub_eq_add_neg] using! (show Allows n (fun x=>F x+ -L x) v _ from hh)
   exact (((Moulin.got j he).smul ballast):Allows n _ _ M).mono (by linarith)
end Boxes

lemma showcase (G:Gauge)(n:ℕ)(P:Patch)(Q:Teller G):∃ r C:ℝ, 0<r∧1≤C∧ ∀ c f(S:StepData c f)(K:Core G S), S.patch=P→Teller.Funds Q S K.tube →∀ v:Dir G c,‖v‖≤r→∀ i:Seats G c f, Allows n (fun x=> K.F0 x i) v C:=by
   obtain ⟨r,C,hC,h1,h2,h3,h⟩:= days G n P Q.bind
   obtain ⟨M,hM,H⟩:=wired G n P Q C (zero_le_one.trans hC) h1
   exact ⟨r,M,h2,hM,fun c f S K hp hf v hv i=> H c f S K hp hf v (h c f S K hf.knobs hp v hv) i⟩
end YM.Planned.PrimaryIntegral295.Belays
