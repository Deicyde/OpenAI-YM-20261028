import YM.UVExtension.Wick.Kindle

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}

structure Juice (G : Gauge) (f : Side) where
  E : ℕ → Config G f → ℝ
  K : ℕ → Config G f → ℝ

def chunk (R : Rep G f) (m : Juice G f) (v : ℝ) : Rep G f :=
    {flight R v with activities:= {R.activities with E:=m.E, K:=m.K}}

variable {ι : Type*} [Fintype ι]
variable (W : ι → Juice G f)

def blend (w : ι→ℝ) : Juice G f := ⟨fun n y=> ∑ i,w i*(W i).E n y,fun n y=> ∑ i,w i*(W i).K n y⟩

lemma strict_budget (h : Intake P T s R) (m : Juice G f) (b : ℝ) (hp : (chunk R m b).activities.Valid R.p
    (incomingE G S.patch.L s) (incomingK G S.patch.L s))
    (hb : b∈ Set.Icc (betaF G s S.patch.L/2) (2*betaF G s S.patch.L)) : Intake P T s (chunk R m b) :=
    ⟨h.ready,⟨h.received.1,h.received.2,h.received.3⟩,⟨h.cap.paths,hp⟩,h.exponent,h.height,h.sizes,hb⟩
lemma retreat (h : Intake P T s R) (b : ℝ) (hb:b∈ Set.Icc (betaF G s S.patch.L/2) (2*betaF G s S.patch.L)) : Intake P T s (flight R b):=
    ⟨h.ready,⟨h.received.1,h.received.2,h.received.3⟩,⟨h.cap.paths,h.cap.labels⟩,h.exponent,h.height,h.sizes,hb⟩
lemma unchanged (R : Rep G f) (m : Juice G f) (b : ℝ) (l d : ℕ) :
    footprints T (chunk R m b) l d=footprints T R l d := rfl
lemma costs_equal (R : Rep G f) (m : Juice G f) (b : ℝ): lengths T (chunk R m b)=lengths T R := rfl
lemma deck (R : Rep G f) (m : Juice G f) (b : ℝ) (l d : ℕ) : troupe T (chunk R m b) l d=troupe T R l d:=rfl

-- EPosition disjunction universal. runtime list basis across REAL footprint.
def madeE (p : LogIndex c f) := ∃ i : ℕ,p=Sum.inl (Sum.inl i)
lemma floatingL {U : Config G f} {y : Directions G f} (V : ι → ℝ) (p : LogIndex c f) :
    let J (m:Juice G f):=chunk R m u
    (X.farLog (J (blend W V)) a Z z p= if madeE p then ∑ i,V i* X.farLog (J (W i)) a Z z p else X.farLog (flight R u) a Z z p) ∧
    (logMoment X a (J (blend W V)) Z y U z p= if madeE p then ∑ i,V i* logMoment X a (J (W i)) Z y U z p else logMoment X a (flight R u) Z y U z p) := by
  intro J
  rcases p with (p|p)|(p|p)
  · simp_rw [if_pos (show madeE (f:=f) (c:=c) (.inl (.inl p)) from ⟨p,rfl⟩)]
    have h (U : Config G f) (k : ℝ) : - (J (blend W V)).activities.regularOccurrence R.p p U*k=
        ∑ i,V i*(-(J (W i)).activities.regularOccurrence R.p p U*k) := by
      change -(masked R.p.threshold (R.activities.reg p).support (fun U=>∑ i,V i*(W i).E p U) U)*k= ∑ i, _ * (-(masked R.p.threshold _ ((W i).E p) U)*k)
      by_cases he : Healthy R.p.threshold (R.activities.reg p).support U
      · rw [masked_eq _ _ _ _ he]; have hh i := masked_eq _ _ ((W i).E p) U he
        change _=∑ i,V i*(-masked _ (R.activities.reg p).support ((W i).E p) _*k); simp_rw [hh,neg_mul, sum_mul,← sum_neg_distrib]; exact sum_congr rfl fun i _=> (by ring)
      rw [masked_ne _ _ _ _ he]; have hh i := masked_ne _ _ ((W i).E p) U he
      change _=∑ i,V i*(-masked _ (R.activities.reg p).support ((W i).E p) _*k); simp [hh]
    exact ⟨h _ _,h _ _⟩
  · simp_rw [if_neg (show ¬madeE (f:=f) (c:=c) (.inl (.inr p)) from by simp [madeE])]
    rcases p with p|p|p|p|p <;> exact ⟨rfl,rfl⟩
  · simp_rw [if_neg (show ¬madeE (f:=f) (c:=c) (.inr (.inl p)) from by simp [madeE])]; exact ⟨rfl,rfl⟩
  simp_rw [if_neg (show ¬madeE (f:=f) (c:=c) (.inr (.inr p)) from by simp [madeE])]; exact ⟨rfl,rfl⟩

lemma pinE (k : LogIndex c f) (h : madeE k) : betaBit k=false:= by rcases h with ⟨i,rfl⟩; rfl

-- z here already physical displacement around mean
variable (R : Rep G f)

def logRay (W : ι → Juice G f) (a : ℝ) (Ñ : ChartRatio G) (z : Air f G) (β : ℂ) (V : ι→ℂ) (i : LogIndex c f) : ℂ :=
    if madeE i then ∑ j,V j * (X.farLog (chunk R (W j) 1) a Ñ (scaled 1 z) i:ℂ) else
    (if betaBit i then β else 1) * (X.farLog (flight R 1) a Ñ (scaled 1 z) i:ℂ)

def valRay (W : ι → Juice G f) (a : ℝ) (Ñ : ChartRatio G) (y : Directions G f) (U : Config G f) (z : Air f G) (β : ℂ) (V : ι→ℂ) (i : LogIndex c f) : ℂ :=
    if madeE i then ∑ j, V j * (logMoment X a (chunk R (W j) 1) Ñ y U (scaled 1 z) i:ℂ) else
    (if betaBit i then β else 1) * (logMoment X a (flight R 1) Ñ y U (scaled 1 z) i:ℂ)
lemma loftR (y : Directions G f) (U : Config G f) (β:ℂ) (hu:0<u) (V:ι→ℂ) (p: LogIndex c f):
    logRay X R W a Z z β V p=(if madeE p then ∑ i,V i* (X.farLog (chunk R (W i) u) a Z (scaled u z) p:ℂ) else (if betaBit p then β/(u:ℂ) else 1) *(X.farLog (flight R u) a Z (scaled u z) p:ℂ)) ∧ valRay X R W a Z y U z β V p=(if madeE p then ∑ i,V i*(logMoment X a (chunk R (W i) u) Z y U (scaled u z) p:ℂ) else (if betaBit p then β/(u:ℂ) else 1)*(logMoment X a (flight R u) Z y U (scaled u z) p:ℂ)) := by
  unfold logRay valRay
  by_cases he:madeE p
  · simp_rw [if_pos he]; have hx : exposure u p=1:= by rw [exposure,pinE p he]; rfl
    constructor <;> apply sum_congr rfl <;> intro i _
    · have ht:= quoted X (R:=chunk R (W i) 1) (Z:=Z) (a:=a) (z:=z) hu p; rw [hx,one_mul] at ht
      change X.farLog _ _ _ _ _=_ at ht
      exact congr_arg (fun x:ℝ=> V i*(x:ℂ)) ht.symm
    have ht:= recess X (R:=chunk R (W i) 1) (Z:=Z) (a:=a) (z:=z) y U hu p; rw [hx,one_mul] at ht; exact congr_arg (fun x:ℝ=> V i*(x:ℂ)) ht.symm
  simp_rw [if_neg he]; rw [quoted X hu,recess X y U hu]; unfold exposure; split_ifs; · push_cast; have hp:(u:ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr hu.ne'; constructor <;> field_simp
  simp
lemma real_rays (y : Directions G f) (U : Config G f) (hu : 0<u) (V : ι → ℝ) (p : LogIndex c f):
    (X.farLog (chunk R (blend W V) u) a Z (scaled u z) p:ℂ)=logRay X R W a Z z u (fun i=>(V i:ℂ)) p ∧
    (logMoment X a (chunk R (blend W V) u) Z y U (scaled u z) p:ℂ)=valRay X R W a Z y U z u (fun i=>(V i:ℂ)) p := by
  obtain ⟨he,hv⟩ := loftR X W R y U (u:ℂ) hu (a:=a) (Z:=Z) (z:=z) (fun i=>(V i:ℂ)) p
  obtain ⟨hh,hp⟩:= floatingL X W (u:=u) (a:=a) (R:=R) (Z:=Z) (z:=scaled u z) (U:=U) (y:=y) V p
  rw [he,hv,hh,hp]; by_cases hr: madeE p <;> simp [hr,hu.ne']

lemma real_k (y : Directions G f) (U : Config G f) (V : ι → ℝ) (k:ℕ) (u a b:ℝ):
    X.bag (chunk R (blend W V) u) a y k=∑ i,V i* X.bag (chunk R (W i) b) a y k ∧ sheath X a (chunk R (blend W V) u) y U k=∑ i,V i * sheath X a (chunk R (W i) b) y U k := by
  dsimp only [Coat.bag, Polar.sheath, chunk, blend]; constructor <;> rw [sum_mul] <;> exact sum_congr rfl fun i _=> mul_assoc ..
end YM.UVExtension.Wick
