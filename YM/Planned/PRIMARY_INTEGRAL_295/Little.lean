import YM.Planned.PRIMARY_INTEGRAL_295.Rails
/-!
# Actual no-hole preGram template on real repertoire & fields at one step

Formal under branch & path convergence hypotheses. Scheme retains S etc
judging chart x near physical evaluation, with full cut B y; not genuine
A/b near masks/holes/forced (those separately promised at every Raw source).
Local anchor windows in one profile will ask correspondence of THIS preGram
to entries of the principal no-hole components actually used. No promises
projection over alternatives; *keeps Q's actual tags transformed correctly*.

ν orientation common. Q tangent via plog of actual relative difference, right
trivialization on produced Q at \u0305V. Negations therefore before contracting
the colored row. \u0305V rotates as group field (copy itself has matching sign,
but E checks chronology via actual occurrences). `F` signed derivative at a=0
of crease approximant, NOT of whole rows (`ℓ_R` transports explicitly frozen).
Calls fderiv actual G.Color vectors. To use, must check existence and equality
of these group derivatives and tsums around contact; never count zeroed fallback.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Little
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars
open Bid (pulled bills Sworn stretch)
open Next.Free Next.Fluctuations Bunks
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {z n k:ℕ} {c f : Side} {S : StepData c f}

structure Core (G:Gauge) (S:StepData c f) where
    tube : Tube G S
    tree : Forest S.ratio
    k : S.Choices
    R : ℕ -- L.till x exact
abbrev Drops (c f : Side) := Signed × (Twin f ⊕ Bond c)
abbrev Seats (G:Gauge) (c f:Side):=Drops c f × G.ColorIndex
abbrev Temps (G:Gauge) (f:Side):=Acres f G→ℝ

namespace Core
variable (K:Core G S)

-- operators in first section universal for any g patch.
def snow (K:Core G S) (i:Bond f):= i∈K.tree.trunks

def reachable (x:Temps G f) : Dir G f:= fun i =>
    let j := (Work.E03.poleEquiv f).symm i
    if j∈K.tree.trunks then 0 else WithLp.toLp 2 fun u:G.ColorIndex=> x (j,u)

def freeze (x:Temps G f) : Temps G f:=fun i=> if K.snow i.1 then x i else 0

def menu (v:Dir G c) (a:Dir G f) : Config G f := increment (replica S.ratio (represent v)) (collect G a)

def venue (s:Signed) (v:Dir G c) : Config G c:=pull s 0 (represent v)

def seek (s:Signed) (v:Dir G c) (a:Temps G f) : Config G f:= pull s 0 (menu (S:=S) v (K.reachable a))

def target (s:Signed) (v:Dir G c) (a:Temps G f) := S.prediction (K.seek s v a) (Push.SectorMeasure.Oriented.choice s K.k)
-- address fee pre actual barrier. uses FULL unclamped short supported predictor from V.

def fro (s:Signed) (v:Dir G c) (x : Twin f): G.Color:=
    K.tube.Xf K.R (K.seek s v 0) x - Pressure.zip (K.tube.Φ K.R (venue s v)) (K.tube.Xn K.R (venue s v)) x

def crock (s:Signed) (v:Dir G c) (x:Bond c): G.Color:= Pressure.Tube.Z S (K.target s v 0) (venue s v) x - Pressure.zip
    (K.tube.Φ' K.R (venue s v)) (K.tube.Xn K.R (venue s v)) x

-- $̅V$ freeze transports even varying field a, E.AFFeq. preserve path label.
def kink (s:Slot) (A B:Config G f) (x:Site f):G.Color := G.adjoint
    (travel (expandAt x A) 0 s.walk) (G.curvature (faceValue (expandAt x B) (s.offset,s.plaq)))

def mbTerm (V U:Config G f) (x:Cell f) (i:ℕ): G.Color:=
    let c:=K.tube.up.row x.2 i
    if c.2.length ≤ K.R then c.1 • kink c.2 V U x.1 else 0

def etched (s:Signed) (v:Dir G c) (a:Temps G f) (x:Twin f) := if x.2 then ∑' i,K.mbTerm
     (K.seek s v 0) (K.seek s v a) x.1 i else shoot K.tube.high (K.seek s v a) x.1

def conf (s:Signed) (v:Dir G c) (a:Temps G f) (x:Bond c) := (-Real.sqrt S.kernel.penalty) •
    G.plog (G.mat (K.target s v a x * (K.target s v 0 x)⁻¹))

def bind (d:Drops c f) (v:Dir G c):G.Color:= Sum.elim (K.fro d.1 v) (K.crock d.1 v) d.2

def jump (d:Drops c f) (v:Dir G c) (a:Temps G f):G.Color:=Sum.elim (K.etched d.1 v a) (K.conf d.1 v a) d.2

def note (d:Drops c f) (v:Dir G c): Temps G f→L[ℝ] G.Color:= fderiv ℝ (K.jump d v) 0

-- one service. included channel weight from real covariance choices.
def ballast := Real.sqrt (Fintype.card Signed:ℝ)⁻¹

-- $D:Seats h charts$ A_h completed, f0 uses sqrt.

def D (v: Dir G c): Matrix (Seats G c f) (Acres f G) ℝ := Matrix.of fun i j=> ballast * (K.note i.1 v (Pi.single j 1)) i.2

def F0 (v:Dir G c):Seats G c f→ℝ:=fun i=>ballast * (K.bind i.1 v) i.2

def fires : Matrix (Acres f G) (Acres f G) ℝ:= Matrix.diagonal fun i=> if K.snow i.1 then 1 else 0

def Gram (v:Dir G c): Matrix (Acres f G) (Acres f G) ℝ:=(K.D v).transpose * K.D v + K.fires

def epoxy (v:Dir G c): Temps G f:= (K.D v).transpose.mulVec (K.F0 v)

lemma fires_mul (v:Temps G f): K.fires.mulVec v= K.freeze v:= by ext i; unfold freeze fires; simp only [Matrix.mulVec_diagonal]; split <;> simp
lemma D_mul (v:Dir G c) (a:Temps G f) (i: Seats G c f): (K.D v).mulVec a i = ballast * K.note i.1 v a i.2:=by
   let L:=K.note i.1 v; let P:=EuclideanSpace.proj (𝕜:=ℝ) i.2
   have he : (∑ j:Acres f G,a j • (Pi.single j 1 : Temps G f))=a:=by ext j; simp [Pi.single_apply,Finset.sum_apply]
   change _=ballast * P (L a)
   nth_rw 2 [← he]; rw [map_sum,map_sum,Finset.mul_sum]
   unfold Matrix.mulVec dotProduct; refine Finset.sum_congr rfl (fun j _=>?_); rw [map_smul,map_smul]; change (_*P _) *_=_*(_*P _); ring

lemma sym (q:Dir G c) : (K.Gram q).IsHermitian:=by
    rw [Gram, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul];
    ext i j; simp only [Matrix.add_apply]; congr 1
    · unfold fires; by_cases h:i=j
      · rw [h]; simp
      simp [h,Ne.symm h]

section Spins
variable (s:Signed) (v:Dir G c)

-- comparator operates on full arrays held **in real direction v**. b+t typed.
def rustic (v:Dir G c):Dir G f:= fun i=>linearCopy S.ratio (collect G v) ((Work.E03.poleEquiv f).symm i)

def outPeak (x:Temps G f): Dir G f:=K.reachable x+rustic (S:=S) v
-- flat affine all uncut rows, not assuming Hank equality in any curtain.

def vastF (x:Temps G f) (i:Twin f):=xLin K.tube.high K.tube.up (pulled (K.outPeak v x) s) i - Pressure.zip (flatF K.tube) (xLin K.tube.low K.tube.down (pulled v s)) i

def vastI (x:Temps G f) (i:Bond c):= zLin S (pulled (K.outPeak v x) s) (pulled v s) i - Pressure.zip (flatI K.tube) (xLin K.tube.low K.tube.down (pulled v s)) i

def spend (x:Temps G f) (i:Drops c f):= Sum.elim (K.vastF i.1 v x) (K.vastI i.1 v x) i.2

def dawn (W:Lines S.ratio.count) (i:Acres f G):ℝ:= (Streets.streamFill S _ (crick S K.tree W v) i.1) i.2

lemma forecast_is (W:Lines S.ratio.count): K.outPeak v (K.dawn v W)= Rails.Ringlets.runway K.tree v W:=by
   funext i; obtain ⟨⟨x,q⟩,rfl⟩:= (Work.E03.poleEquiv f).surjective i
   change K.reachable _ (x,coord q)+linearCopy _ _ _ = _
   have he:= axisEquiv.symm_apply_apply q; unfold Rails.Ringlets.runway Bid.stretch;
   unfold reachable; simp only [show (Work.E03.poleEquiv f) (x,q)=(x, Exterior.coord q) from rfl,show axisEquiv.symm (coord q)=q from he, show (Work.E03.poleEquiv f).symm (x,coord q)=(x,q) from (Work.E03.poleEquiv f).symm_apply_apply (x,q)]
   by_cases hu : (x,q)∈K.tree.trunks
   · simp only [hu]; simp
   simp only [hu]; apply (add_comm ..).trans; congr; ext j
   change (Streets.streamFill S _ _ _) _=_; unfold Streets.streamFill; rw [ContinuousLinearMap.pi_apply,dif_neg hu]; rfl
lemma dawn_iced (W:Lines S.ratio.count): K.freeze (K.dawn v W)=0:=by
   funext i; unfold freeze; split<;> rename_i h; swap; · rfl
   unfold snow at h; unfold dawn Streets.streamFill; rw [ContinuousLinearMap.pi_apply,dif_pos h]; rfl

lemma full_zero (i:Drops c f) {Q:Teller G} {H H':Bed} (hh:Rails.Ringlets Q K.tube H H') :
    K.spend v (K.dawn v K.tube.R.A0) i=0 := by
   obtain ⟨s,p|p⟩:=i
   · change K.vastF _ _ _ _=_; unfold vastF; rw [forecast_is]; exact (Rails.Ringlets.cool_row s K.tree K.tube v hh K.k).1 _
   change K.vastI _ _ _ _=_; unfold vastI; rw [forecast_is]; exact (Rails.Ringlets.cool_row s K.tree K.tube v hh K.k).2 _
end Spins
end Core
end YM.Planned.PrimaryIntegral295.Little
