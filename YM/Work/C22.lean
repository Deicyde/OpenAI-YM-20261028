import YM.Analysis.Polydisc
import YM.Bid.Grow

/-!
# Inner product at separate hot profiles

First keep both widths, and specialize time variables to purely imaginary:
the two vectors computed recursively then give actual GNS plants; the Gram
calculation uses opposite heights, reverse *and* reflected tokens.
Continue along a single complex parameter instead of doing a
padding comparison: any prescribed array of real times times that
parameter (conjugate the parameter in the first/antilinear slot).
Strict height and gap inequalities still suffice on an open strip.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.C22
open Function Set Filter Complex
open Mink Boundary OS Word
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff

variable {G : Gauge} {L : Register G} {n m : ℕ} {S T : Table L} {V : Chamber T timeAxis}

-- Shot or intermediate train with preceding reference Z,X of padding q
private def fromRef (B : Small S V) (p q : ℝ≥0) :
    ∀ {n}, Times n → SpacePoints n → (Fin n → S.Union) → ℂ → Space3 → V.H
  | 0,_,_,_,_,_ => V.omega
  | n+1,z,x,v,Z,X =>
      Small.rip (z 0-Z) (q+p) (x 0-X) ((B.bar p (v 0)) (B.trainB p n (Fin.tail z)
        (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

private lemma fromTrain (B : Small S V) (p : ℝ≥0) (z : Times n) (x : SpacePoints n)
    (v : Fin n → S.Union) (Z : ℂ) (X : Space3) :
    B.trainB p n z x v Z X = fromRef B p p z x v Z X := by
  cases n <;> simp only [fromRef,Small.trainB]

private lemma fromPoint (B : Small S V) (p : ℝ≥0) (v : Fin n → S.Union) (y : Heights n) (k : Points n) :
    B.shot p n v y k = fromRef B p 0 (shift k y) (trace k) v 0 0 := by
  cases n <;> simp only [Small.shot,fromRef,zero_add,sub_zero]

private lemma nextRef (B : Small S V) (p q : ℝ≥0) (z : Times (n+1)) (x : SpacePoints (n+1))
    (v : Fin (n+1) → S.Union) (Z : ℂ) (X : Space3) :
    fromRef B p q z x v Z X = Small.rip (z 0-Z) (q+p) (x 0-X) ((B.bar p (v 0))
      (fromRef B p p (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0))) := by
  rw [← fromTrain]; rfl

-- Hypotheses actually needed on imaginary coordinates in fromRef.
private def Room (p q : ℝ≥0) (y : Heights n) (Y : ℝ) : Prop :=
    (∀ i, ↑(q+p) < y i - Y) ∧ (∀ i j : Fin n, i < j → ↑(p+p) < y j - y i)

private lemma tailRoom {p q : ℝ≥0} {y : Heights (n+1)} {Y : ℝ} (h : Room p q y Y) :
    Room p p (Fin.tail y) (y 0) := ⟨fun i => h.2 0 i.succ (Fin.succ_pos i),
      fun i j hij => h.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩

private def pinned (e : S.Tag) := S.pin e.1 e.2
private def raw (e : S.Tag) : L.Token := ⟨e.1,S.representative e.1 e.2⟩
private def iz (y : ℝ) : ℂ := ↑y*I

private lemma oneSlab (e : L.Token) {p : ℝ≥0} (hp : 0<p) :
    Slab timeAxis (p+p) [(position 0 p,e)] := by
  have hh : YM.time (position 0 p) = p := by simp
  refine ⟨add_pos hp hp, ⟨locations.mpr (by simp),?_⟩,?_⟩
  · intro i hi; obtain rfl := List.mem_singleton.mp hi
    rw [show (position _ _ : E4) timeAxis = _ from hh]
    exact hp
  intro i hi; obtain rfl := List.mem_singleton.mp hi
  rw [show (position _ _ : E4) timeAxis = _ from hh]; simp [hp]

private lemma euclideanRef {B : Small S V} {A : Spread V}
    (link : B.concretized A) {p : ℝ≥0} (hp : 0<p)
    (q : ℝ≥0) (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag) (Y : ℝ) (X : Space3)
    (h : Room p q y Y) :
    ∃ b : Future L timeAxis,
      b.val = List.ofFn (fun i => (position (x i-X) (y i-Y-(q:ℝ)),raw (v i))) ∧
        fromRef B p q (iz ∘ y) x (pinned ∘ v) (iz Y) X = V.GNS.plant b := by
  induction n generalizing q Y X with
  | zero => exact ⟨air timeAxis,List.ofFn_zero.symm,rfl⟩
  | succ n ih =>
    obtain ⟨b,hb,hplant⟩ := ih p (Fin.tail y) (Fin.tail x) (Fin.tail v) _ (x 0) (tailRoom h)
    let r := (y 0 - Y - ↑(q+p)).toNNReal
    have hg : 0 < y 0 - Y - ↑(q+p) := sub_pos.mpr (h.1 0)
    have hr : 0<r := Real.toNNReal_pos.mpr hg
    have hco : (r:ℝ) = y 0 - Y - ↑(q+p) := Real.coe_toNNReal _ hg.le
    let w := entering (oneSlab (raw (v 0)) hp) b
    let s := Small.bufferF (x 0-X)
    refine ⟨travel (over w s) r, ?_, ?_⟩
    · dsimp only [travel,over,w,s,Small.bufferF,entering,linked,raised]
      rw [hb]; simp only [carry,List.singleton_append,List.map_cons,List.map_ofFn]
      rw [List.ofFn_succ]
      congr 1
      · refine Prod.ext (ext_by ?_ ?_) rfl
        · simp
        simp [hco]; ring
      apply congr_arg List.ofFn
      funext i; refine Prod.ext (ext_by ?_ ?_) rfl
      · simp [Fin.tail]
      simp [Fin.tail,hco]; ring
    rw [nextRef]
    have hI : Small.interval (iz (y 0)-iz Y) (q+p) = OS.Semigroup.duration r := by
      apply Complex.ext <;> simp [Small.interval,iz,hco,OS.Semigroup.duration]
    have he : B.bar p (pinned (v 0)) = A.place (p+p) [(position 0 p,raw (v 0))] :=
      link (v 0).1 (v 0).2 p hp
    change V.flow.F (Small.interval (iz (y 0) - iz Y) (q+p)) (V.flow.U s
      ((B.bar p (pinned (v 0))) (fromRef B p p (iz ∘ Fin.tail y) (Fin.tail x) _ (iz (y 0)) (x 0)))) = _
    rw [show Fin.tail (pinned ∘ v) = pinned ∘ Fin.tail v from rfl, hplant,hI,V.flow.roots_heat hr,he]
    rw [A.reads (oneSlab (raw (v 0)) hp) b,← V.across,← V.atBirth]

private lemma roomPositive {p : ℝ≥0} {y : Heights n} (h : Room p 0 y 0) : y ∈ positiveHeight n := by
  refine ⟨fun i j hij => sub_pos.mp ((p+p).coe_nonneg.trans_lt (h.2 i j hij)),fun i => ?_⟩
  exact sub_pos.mp ((0+p).coe_nonneg.trans_lt (h.1 i))

private lemma eastBoth {p q : ℝ≥0} {y : Heights n} {z : Heights m}
    (h : Room p 0 y 0) (g : Room q 0 z 0) : Bid.bothH y z ∈ east (n+m) := by
  have hp := roomPositive h; have hq := roomPositive g
  intro i j hij
  cases i using Fin.addCases <;> cases j using Fin.addCases <;> simp only [Bid.bothH,Fin.append_left,Fin.append_right]
  · exact neg_lt_neg (hp.1 (Fin.rev_lt_rev.mpr hij))
  · exact lt_trans (neg_lt_zero.mpr (hp.2 _)) (hq.2 _)
  · simp only [Fin.lt_def,Fin.val_natAdd,Fin.val_castAdd] at hij; omega
  exact hq.1 (by simpa using hij)

private def bothSpace (x : SpacePoints n) (r : SpacePoints m) : SpacePoints (n+m) :=
  Fin.append (fun i : Fin n => x i.rev) r

private lemma reflect_position (x : Space3) (t : ℝ) :
    Ortho.move (Signed.reflect timeAxis) (position x t) = position x (-t) := by
  ext1 i; refine Fin.lastCases ?_ ?_ i
  · simp only [Signed.mirrored,position,WithLp.ofLp_toLp, if_true,Fin.snoc_last]
  intro j; simp only [Signed.mirrored,position,WithLp.ofLp_toLp,Fin.castSucc_ne_last,if_false,Fin.snoc_castSucc]

private lemma reverse_ofFn {M : Type*} (v : Fin n → M) :
    (List.ofFn v).reverse = List.ofFn (fun i : Fin n => v i.rev) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [Fin.rev]
  congr 2; omega

private def bothRaw (v : Fin n → L.Token) (w : Fin m → L.Token) : Fin (n+m) → L.Token :=
    Fin.append (fun i : Fin n => L.reflectedToken timeAxis (v i.rev)) w

-- Identify the literal doubled word in the Table.gram formula.
private lemma ofFnJoined (y : Heights n) (z : Heights m) (x : SpacePoints n) (r : SpacePoints m)
    (v : Fin n → L.Token) (w : Fin m → L.Token) :
    reflect (List.ofFn (fun i => (position (x i) (y i),v i))) timeAxis ++
      List.ofFn (fun i => (position (r i) (z i),w i)) =
      realize (bothRaw v w) (place (bothSpace x r) (Bid.bothH y z)) := by
  rw [reflectedPoint,reverse_ofFn,List.map_ofFn,← List.ofFn_fin_append]; unfold realize
  congr 1; funext i
  cases i using Fin.addCases <;> simp [bothRaw,bothSpace,place,Bid.bothH,reflect_position]

private lemma class_star {J : StarOp S} {h : S.RealSpin} (hr : starRead J h) (v : S.Tag) :
    J (pinned v) = pinned (S.classTokens (L.reflectedToken timeAxis (raw v))) := by
  unfold pinned; rw [hr]
  congr 1
  change S.adj h _ _ _ = S.project _ (L.adj v.1 timeAxis (S.representative _ v.2))
  rw [← S.adj_project,S.rep]

private lemma euclideanShot {B : Small S V} {A : Spread V}
    (link : B.concretized A) {p : ℝ≥0} (hp : 0<p)
    (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag)
    (h : Room p 0 y 0) :
    ∃ b : Future L timeAxis,
      b.val = List.ofFn (fun i => (position (x i) (y i),raw (v i))) ∧
        fromRef B p 0 (iz ∘ y) x (pinned ∘ v) 0 0 = V.GNS.plant b := by
  simpa only [iz,NNReal.coe_zero, Complex.ofReal_zero,zero_mul,sub_zero] using
    euclideanRef link hp 0 y x v 0 0 h

-- No common-width restrictions in this lemma. S.classTokens is used even on T.
private lemma onImag {B : Small S V} {A : Spread V} {J : StarOp S} {H : S.RealSpin}
    {F : Waves S} (link : B.concretized A) (hr : starRead J H)
    (hf : F.Region T) (hT : T.Symmetric) (hw : T.respects S)
    {p q : ℝ≥0} (hp : 0<p) (hq : 0<q) (y : Heights n) (z : Heights m)
    (x : SpacePoints n) (r : SpacePoints m) (v : Fin n → S.Tag) (w : Fin m → S.Tag)
    (h : Room p 0 y 0) (g : Room q 0 z 0) :
    inner ℂ (fromRef B p 0 (iz ∘ y) x (pinned ∘ v) 0 0)
      (fromRef B q 0 (iz ∘ z) r (pinned ∘ w) 0 0) =
    F.F (n+m) (iz ∘ Bid.bothH y z) (bothSpace x r) (Bid.bothT (pinned ∘ v) (pinned ∘ w) J) := by
  obtain ⟨a,ha,H₁⟩ := euclideanShot link hp y x v h
  obtain ⟨b,hb,H₂⟩ := euclideanShot link hq z r w g
  rw [H₁,H₂,V.GNS.measure]; unfold Table.gram; rw [ha,hb]
  let u : Fin (n+m) → L.Token := bothRaw (raw ∘ v) (raw ∘ w)
  have he := ofFnJoined y z x r (raw ∘ v) (raw ∘ w)
  simp only [Function.comp_apply] at he; rw [he,T.readAt]
  have ht : Bid.bothT (pinned ∘ v) (pinned ∘ w) J = pinned ∘ (S.classTokens ∘ u) := by
    funext i; cases i using Fin.addCases
    · simpa only [Bid.bothT,Fin.append_left,Function.comp_apply,u,bothRaw] using class_star hr _
    simp only [Bid.bothT,Fin.append_right,Function.comp_apply,u,bothRaw]
    unfold pinned raw Table.classTokens; rw [S.rep]
  rw [ht]
  exact ((hf.roots (n+m) (S.classTokens ∘ u) _ _ (eastBoth h g)).trans
    (S.at_project T hT hw (clear (eastBoth h g) _) u)).symm

private lemma fromDiff (B : Small S V) (p q : ℝ≥0) (z : ℂ → Times n) (Z : ℂ → ℂ)
    (x : SpacePoints n) (X : Space3) (v : Fin n → S.Union) (c : ℂ)
    (h : Room p q (fun i => (z c i).im) (Z c).im)
    (hx : ∀ i, DifferentiableAt ℂ (fun d => z d i) c) (hu : DifferentiableAt ℂ Z c) :
    DifferentiableAt ℂ (fun d => fromRef B p q (z d) x v (Z d) X) c := by
  induction n generalizing q Z X with
  | zero => exact differentiableAt_const _
  | succ n ih =>
    let f (d : ℂ) := Small.interval (z d 0 - Z d) (q+p)
    have hf : DifferentiableAt ℂ f c :=
      (differentiableAt_const _ |>.mul ((hx 0).sub hu)).sub (differentiableAt_const _)
    have hI : f c ∈ OS.Semigroup.inside := (Small.down _ _).mpr (h.1 0)
    have hb := ih p (fun c => Fin.tail (z c)) (fun c => z c 0) (Fin.tail x) (x 0) (Fin.tail v)
      (tailRoom h) (fun i => hx i.succ) (hx 0)
    let u := V.flow.U (Small.bufferF (x 0-X))
    let g := B.bar p (v 0)
    simp_rw [nextRef]
    exact ((V.flow.localHeat (f c) hI).differentiableAt.comp c hf).clm_apply
      (u.differentiableAt.comp c (g.differentiableAt.comp c hb))

-- The first vector need not have a conjugation in its Hilbert space.
-- Use the scalar conjugation and antilinearity in the slope calculation.
private lemma fromInner {D : Hilbert} {f g : ℂ → D} {c : ℂ}
    (hf : DifferentiableAt ℂ f (star c)) (hg : DifferentiableAt ℂ g c) :
    DifferentiableAt ℂ (fun d => inner ℂ (f (star d)) (g d)) c := by
  have hs : Tendsto (star : ℂ → ℂ) (𝓝[≠] c) (𝓝[≠] star c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_star.tendsto c).mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact fun he => hd (star_injective he)
  let w : ℂ := inner ℂ (deriv f (star c)) (g c)+inner ℂ (f (star c)) (deriv g c)
  suffices H : HasDerivAt (fun d => inner ℂ (f (star d)) (g d)) w c from H.differentiableAt
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h₁ := (hf.hasDerivAt.tendsto_slope.comp hs).inner (𝕜:=ℂ)
    (hg.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:={c}ᶜ)))
  have h₂ := (tendsto_const_nhds (x:= f (star c))).inner (𝕜:=ℂ) hg.hasDerivAt.tendsto_slope
  refine (h₁.add h₂).congr' (Eventually.of_forall fun d => ?_)
  simp [slope_def_module,inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]; ring

-- profile and imaginary part along the one-complex-dimensional path
private def alongTimes (y : Heights n) (r : Points n) (c : ℂ) : Times n := fun i =>
    iz (y i) + c * ↑(YM.time (r i))
private def alongImag (y : Heights n) (r : Points n) (t : ℝ) : Heights n := fun i =>
    y i+t*YM.time (r i)

private lemma along_im (y : Heights n) (r : Points n) (c : ℂ) :
    (fun i => (alongTimes y r c i).im)=alongImag y r c.im := by
  funext i; simp [alongTimes,alongImag,iz]

private lemma along_pure (y : Heights n) (r : Points n) (t : ℝ) :
    alongTimes y r (iz t)=iz ∘ alongImag y r t := by
  funext i; simp only [alongTimes,alongImag,Function.comp_apply,iz]; push_cast; ring

private lemma along_both (y : Heights n) (z : Heights m) (r : Points n) (s : Points m) (t : ℝ) :
    alongImag (Bid.bothH y z) (Bid.bothP r s) t = Bid.bothH (alongImag y r (-t)) (alongImag z s t) := by
  funext i; cases i using Fin.addCases <;> simp [Bid.bothH,Bid.bothP,alongImag]; ring

private lemma along_room {p : ℝ≥0} {y : Heights n} (h : Room p 0 y 0) (r : Points n) :
    ∀ᶠ t : ℝ in 𝓝 0, Room p 0 (alongImag y r t) 0 := by
  let S := {v : Heights n | Room p 0 v 0}
  have ho : IsOpen S := by
    have he : S = (⋂ i : Fin n, {v : Heights n | ↑(0+p)<v i - (0:ℝ)}) ∩
        ⋂ (i : Fin n) (j : Fin n) (_ : i<j), {v : Heights n | ↑(p+p) < v j - v i} := by
      ext1; simp [S,Room]
    rw [he]
    refine IsOpen.inter (isOpen_iInter_of_finite fun i => ?_)
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => ?_) <;>
      exact isOpen_lt continuous_const (by fun_prop)
  have hy : Continuous (alongImag y r) := by unfold alongImag; fun_prop
  have H : alongImag y r 0 = y := by funext; simp [alongImag]
  have hS : alongImag y r 0 ∈ S := H.symm ▸ h
  exact (hy.tendsto 0).eventually (ho.mem_nhds hS)

private lemma along_go {B : Small S V} (v : Fin n → S.Union) {p : ℝ≥0} (y : Heights n) (r : Points n)
    {c : ℂ} (h : Room p 0 (alongImag y r c.im) 0) :
    DifferentiableAt ℂ (fun d => fromRef B p 0 (alongTimes y r d) (trace r) v 0 0) c := by
  rw [← along_im] at h
  exact fromDiff B p 0 (alongTimes y r) (fun _ => 0) _ 0 v c h
    (fun i => by dsimp only [alongTimes]; fun_prop) (differentiableAt_const _)

private lemma pointJoined {B : Small S V} {A : Spread V} {J : StarOp S} {H : S.RealSpin}
    {F : Waves S} (link : B.concretized A) (hr : starRead J H)
    (hf : F.Region T) (hT : T.Symmetric) (hw : T.respects S)
    {p q : ℝ≥0} (hp : 0<p) (hq : 0<q) (y : Heights n) (z : Heights m)
    (r : Points n) (s : Points m) (v : Fin n → S.Tag) (w : Fin m → S.Tag)
    (h : Room p 0 y 0) (g : Room q 0 z 0) :
    inner ℂ (B.shot p n (pinned ∘ v) y r) (B.shot q m (pinned ∘ w) z s) =
    F.restricted (Bid.bothT (pinned ∘ v) (pinned ∘ w) J) (Bid.bothH y z) (Bid.bothP r s) := by
  let z₁ := alongTimes y r
  let z₂ := alongTimes z s
  let Z := alongTimes (Bid.bothH y z) (Bid.bothP r s)
  let x := bothSpace (trace r) (trace s)
  let a : ℂ → V.H := fun c => fromRef B p 0 (z₁ c) (trace r) (pinned ∘ v) 0 0
  let b : ℂ → V.H := fun c => fromRef B q 0 (z₂ c) (trace s) (pinned ∘ w) 0 0
  let l (c : ℂ) := inner ℂ (a (star c)) (b c)
  let k (c : ℂ) := F.F (n+m) (Z c) x (Bid.bothT (pinned ∘ v) (pinned ∘ w) J)
  have hs : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0:ℝ))
  obtain ⟨δ,hδ,hstrip⟩ := Metric.eventually_nhds_iff.mp
    ((hs.eventually (along_room h r)).and (along_room g s))
  let U : Set ℂ := im ⁻¹' Ioo (-δ) δ
  have hu : IsOpen U := isOpen_Ioo.preimage continuous_im
  have hc : IsPreconnected U := Convex.isPreconnected ((convex_Ioo (-δ) δ).linear_preimage imCLM.toLinearMap)
  have hzero : (0:ℂ)∈U := ⟨neg_lt_zero.mpr hδ,hδ⟩
  have hroom (c : ℂ) (Hc : c ∈ U) :
      Room p 0 (alongImag y r (-c.im)) 0 ∧ Room q 0 (alongImag z s c.im) 0 :=
    hstrip (by simpa only [Real.dist_eq,sub_zero,abs_lt] using (show -δ<c.im ∧ c.im<δ from Hc))
  have hl : DifferentiableOn ℂ l U := by
    intro c Hc
    obtain ⟨hc,hb⟩ := hroom c Hc
    exact (fromInner (D:=V.H) (f:=a) (g:=b) (c:=c) (along_go _ _ _ (by simpa using hc))
      (along_go _ _ _ hb)).differentiableWithinAt
  have hk : DifferentiableOn ℂ k U := by
    have ht : Differentiable ℂ Z := by
      unfold Z alongTimes; fun_prop
    refine (hf.hol (n+m) _ x).comp ht.differentiableOn fun c Hc => ?_
    change (fun i => (alongTimes _ _ c i).im) ∈ east _
    rw [along_im,along_both]; exact eastBoth (hroom c Hc).1 (hroom c Hc).2
  have pure (t : ℝ) (hpure : iz t ∈ U) : l (iz t)=k (iz t) := by
    dsimp only [l,k,a,b,z₁,z₂,Z]
    rw [show star (iz t)=iz (-t) by simp [iz,mul_comm],along_pure,along_pure,along_pure,along_both]
    have he := hroom (iz t) hpure
    rw [show (iz t).im=t by simp [iz]] at he
    exact onImag link hr hf hT hw hp hq _ _ _ _ v w he.1 he.2
  have hEq : EqOn l k U := by
    refine (hl.analyticOnNhd hu).eqOn_of_preconnected_of_frequently_eq (hk.analyticOnNhd hu) hc hzero ?_
    intro hn
    have hh : Tendsto iz (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hi : Continuous iz := continuous_ofReal.mul continuous_const
        simpa [iz] using ((hi.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with i hi
      change iz i ≠ 0; simp [iz,(mem_Ioi.mp hi).ne']
    obtain ⟨t,ht,Ht⟩ := ((hh.eventually hn).and ((hh.mono_right nhdsWithin_le_nhds).eventually
      (hu.mem_nhds hzero))).exists
    exact ht (pure t Ht)
  have he := hEq (show (1:ℂ)∈U from ⟨neg_lt_zero.mpr hδ,hδ⟩)
  have hat {n : ℕ} (y : Heights n) (r : Points n) : alongTimes y r 1=shift r y := by
    funext i; simp [alongTimes,iz,shift,add_comm]
  have hx : trace (Bid.bothP r s)=x := by
    funext i; cases i using Fin.addCases <;> simp [Bid.bothP,trace,x,bothSpace]
  dsimp only [l,k,a,b,Z,z₁,z₂] at he; rw [star_one,hat,hat,hat,← hx] at he
  rw [fromPoint,fromPoint]; exact he

private lemma ample_room {p : ℝ≥0} {y : Heights n} (h : Small.ample p y) : Room p 0 y 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [zero_add,sub_zero]; linarith [h.2 i,p.coe_nonneg]
  rw [NNReal.coe_add]; linarith [h.1.2.2 i j hij,p.coe_nonneg]

private lemma tagOrigins (P : DiffPlan S) (hS : S.Symmetric) (hP : P.Inclusions S) (v : Fin n → S.Union) :
    ∃ e : Fin n → S.Tag, pinned ∘ e = v := by
  choose d x h using fun i => P.covered hS hP (v i)
  exact ⟨fun i => ⟨d i,x i⟩,funext h⟩

theorem answer : YM.Bid.C22 := by
  intro G L S T V P A B F H J hr hd _ hT
  refine ⟨fun n m v w p q y z _ _ h g r s => ?_⟩
  obtain ⟨v',rfl⟩ := tagOrigins P H.head.laws.toSymmetric H.rises v
  obtain ⟨w',rfl⟩ := tagOrigins P H.head.laws.toSymmetric H.rises w
  exact pointJoined hd.linked.stature.bits hr hd.reach H.adopted.laws.toSymmetric hT
    h.1.1 g.1.1 y z r s v' w' (ample_room h) (ample_room g)
end YM.Work.C22
