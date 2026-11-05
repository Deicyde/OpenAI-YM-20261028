import YM.Contacts.Layers.Uniform

/-!
# Signed-residue tree estimate

Usable on families specified with finitely many scale parameters, with a simple grammar
(proof-tree). Arbitrary arity using the product rule (multiply two already priced expressions
any number of times), and arbitrary multiscale depth. The previously constructed theory,
basis-independent field filtration, and fixed, real and O(4)-equivariant detection prescription
on the unselected table. Readers **at every character** in addition to the unselected law.

Costs here are *before testing at any of the contact strata*, on the geometry of the clusters
involved. Clearance & size assumptions are pointwise; don't feed any contacts into this theorem.
In particular every size lies in (0,1] -- there is no lower ratio bound. An overall group of fixed
exteriors can take scale 1 with simple separation bounds and no root match. Several collision
groups can enter that product reader. Include arbitrary nonnegative weights/horizons and all parent,
child center conventions (in the conditions about palettes). Families in the uniformity statements
needn't be continuous.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set Metric MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {W I : Type}
variable {F : Extraction.Order} {Z : Final C F S} {M : Devices Z.sector.derivatives}
variable {φ : Filter W} {T : W→ℝ} {s u v c : ℝ}

lemma tighter (hT : Tendsto T φ atTop)[φ.NeBot] {f g : W→ℝ} (h : RateIs φ T f (-s))(k : RateIs φ T g (-u)) (L : ℝ)
     (hh : ∀ᶠ t in φ,f t ≤ L*g t) : u ≤ s := by
   by_contra! h'; have he:= h.overtakes (((RateLE.const L hT).mul (k.pays hT)).mono (le_of_eq (zero_add _))) hT (neg_lt_neg h')
   obtain ⟨t,hl,hx⟩:=(he.and hh).exists; exact hl.not_ge hx

lemma from_span {p q : W→E4}{f : W→ℝ} (h : RateIs φ T f (-s)) (hT : Tendsto T φ atTop) (L : ℝ)
     (hh : ∀ᶠ t in φ, ‖p t-q t‖ ≤ L*f t) : RateLE φ T (fun t=> p t-q t) (-s) :=
  RateLE.of_norm_le (((RateLE.const L hT).mul (h.pays hT)).mono ((zero_add _).le)) hh
lemma from_gap {p q : W→ E4}{f : W→ℝ} (h : RateIs φ T f (-s)) (hT : Tendsto T φ atTop) (L : ℝ) (hL : 0<L)
     (hh : ∀ᶠ t in φ, L*f t ≤ ‖p t-q t‖) : Intervals φ T s (sole ∘ p) (sole ∘ q):= by
  intro v hv; filter_upwards [(((RateIs.const hT hL).mul h).swap (zero_add (-s))).overtakes (RateLE.exp (-v) hT) hT (neg_lt_neg hv),hh] with i hi hc using fun a b=> hi.trans_le hc

def Inspect (U : Set W) (r : W→ℝ)(x : W→E4) (A : Set (W→E4)) := ∃ C:ℝ, ∀ y∈A, ∀ t∈U, ‖y t-x t‖ ≤ C*r t
def Window (M : Devices Z.sector.derivatives) (U : Set W)(w : ℕ) (x : W→E4) (A : Set (W→ E4)) := ∀ y∈A,∀ t∈U, ‖y t-x t‖ ≤ M.clearance w
def Separate (U : Set W) (A B : Set (W→ E4)) (r : W→ℝ) := ∃ C > (0:ℝ),∀ x∈ A, ∀ y∈ B,∀ t∈U,C * r t ≤ ‖x t-y t‖
def Small (U : Set W) (r s : W→ℝ) := ∃ C:ℝ,∀ t∈U,r t ≤ C*s t

inductive Ticket (Z : Final C F S) (M : Devices Z.sector.derivatives) (R : I → W→ℝ) (U : Set W) :
    (A : Set (W → E4)) → I → (W → ℝ) → (W → Expression Z.sector.derivatives) → Prop where
  | leaf {A d i} (x : W→ E4) (p : W→ S.Field d) (hx : x∈ A) (h : ∃ P : ℝ,∀ t∈U, ‖p t‖ ≤ P) :
      Ticket Z M R U A i (fun t=> R i t ^ (-(d:ℝ))) (fun t=> insertField M.basis (x t) d (p t))
  | unit {A i} : Ticket Z M R U A i 1 1
  | times {A B i p q e f} : Ticket Z M R U A i p e → Ticket Z M R U B i q f → Separate U A B (R i) → Ticket Z M R U (A∪ B) i (p*q) (e*f)
  | carry {A i p e j} (h : Ticket Z M R U A i p e) (x : W→ E4) (hx : x∈A) (hp : Inspect U (R i) x A) (hs : Small U (R i) (R j)) : Ticket Z M R U A j p e
  -- can be used also inside other nodes: ratio gain on EACH such step in the physical weight
  | residual {A i p e j} (h : Ticket Z M R U A i p e) (x : W→ E4) (w : ℕ) (hx : x∈A) (hp : Inspect U (R i) x A) (hs : Small U (R i) (R j)) (hw : Window M U w x A) : Ticket Z M R U A j (fun t=> p t*((R i t / R j t)^(w+1:ℝ))) (e-statedProject M w x e)
  -- no ratio smallness here (important for tails)
  | project {A i p e j} (h : Ticket Z M R U A i p e) (x : W→ E4) (w : ℕ) (hx : x∈A) (hp : Inspect U (R i) x A) (hw : Window M U w x A) : Ticket Z M R U {x} j
          (fun t=> p t*((R i t / R j t)^(w:ℝ))) (fun t=> M.insertRow (x t) w (e t))
  | widen {A B i p e} (h : Ticket Z M R U A i p e) (hp : A ⊆ B) : Ticket Z M R U B i p e

namespace Ticket
variable {V A' B' : Type} {φ : Filter ℕ} {T : ℕ→ ℝ} {R : I → W→ℝ} {U : Set W} {f : ℕ→ W} {p : W→ ℝ} {e : W → Expression Z.sector.derivatives} {A B: Set (W → E4)}{x : W→E4}{i j : I}

def route (f : ℕ→ W) (A : Set (W→ E4)) : Set (ℕ→ E4) := (fun p=> p ∘ f) '' A
variable (hR : Ride R φ T f) (hF : ∀ i,f i∈U)
include hF
variable (hs : RateIs φ T (R i ∘ f) (-s))(hs' : s∈ Icc (0:ℝ) 1)
include hR hs
lemma size_path (hx : Inspect U (R i) x A) : Habitat φ T s (x∘f) (route f A):= by
    obtain ⟨L,hh⟩:=hx; rintro y ⟨z,hz,rfl⟩; exact from_span hs hR.height L (Eventually.of_forall fun i=> hh _ hz _ (hF i))
omit hs hR in
lemma fits_path {w : ℕ} (hv : Window M U w x A) : Fits M φ w (x ∘ f) (route f A) := by
    rintro y ⟨z,hz,rfl⟩; exact Eventually.of_forall fun i=> hv _ hz _ (hF i)
lemma cross_path (hx : Separate U A B (R i)): Cross φ T s (route f A) (route f B):= by
    obtain ⟨L,hp,h⟩:=hx; rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩; exact from_gap hs hR.height L hp (Eventually.of_forall fun i=> h _ hx _ hy _ (hF i))
lemma smaller_path [φ.NeBot] (hu : RateIs φ T (R j ∘ f) (-u)) (hv : Small U (R j) (R i)) : s ≤ u:= tighter hR.height hu hs hv.choose (Eventually.of_forall fun i=> hv.choose_spec _ (hF i))

variable [φ.NeBot] (H : Services C F S)
include hs' H
lemma wallet (h : Ticket Z M R U A i p e) : ∃ c, RateIs φ T (p ∘ f) c ∧ Funds Z M φ T (route f A) s c (e ∘ f):= by
   induction h generalizing s with
   | @leaf A d i x p hx hp =>
     refine ⟨_, hs.rpow (-(d:ℝ)), Fine.funds ?_ hs'.2⟩; refine Fine.field hR.height (x:= x∘ f) ⟨x,hx,rfl⟩ (p:=p ∘ f) ?_; exact (RateLE.absBound _ hR.height (Eventually.of_forall fun i=> hp.choose_spec _ (hF i))).mono (by linarith only)
   | unit => exact ⟨_,RateIs.const hR.height zero_lt_one,(Fine.unitOne hR.height).funds hs'.2⟩
   | @times A B i p q e E h h' he ih ih'=>
     obtain ⟨c,hc,hx⟩:=ih hs hs'; obtain ⟨d,hd,hy⟩:=ih' hs hs'; have hu: route f (A ∪ B)= route f A ∪ route f B := Set.image_union ..; rw [hu]; exact ⟨_,hc.mul hd,Funds.times hR.height hx hy (cross_path hR hF hs he) hs'.2⟩
   | @widen A B i p e h hp ih=>
     obtain ⟨c,h,hk⟩:= ih hs hs'; exact ⟨_,h,hk.mono le_rfl (Set.image_mono hp)⟩
   | @carry A i p e j h x hx hp hv ih =>
     obtain ⟨u,hu,he⟩:= hR.entries i; obtain ⟨k,hh,hx'⟩:= ih he hu; exact ⟨k,hh,hx'.coarsen hR.height H (size_path hR hF he hp) ⟨x,hx,rfl⟩ (smaller_path hR hF hs he hv) hu.2 hs'.1⟩
   | @residual A i p e j h x w hx hp hv hT ih =>
     obtain ⟨u,hu,he⟩:= hR.entries i; obtain ⟨k,hh,hx'⟩:= ih he hu; refine ⟨_, hh.mul ((he.div hs).rpow (w+1:ℝ)), Funds.mono (hx'.drop hR.height H (size_path hR hF he hp) ⟨x,hx,rfl⟩ (fits_path hF hT) (smaller_path hR hF hs he hv) hu.2 hs'.1) (by linarith only) (by rfl)⟩
   | @project A i p e j h x w hx hp hv ih=>
     obtain ⟨u,hu,he⟩:= hR.entries i; obtain ⟨k,hh,hx'⟩:= ih he hu; refine ⟨_, hh.mul ((he.div hs).rpow (w:ℝ)), Fine.funds (Fine.field (x:=x ∘ f) hR.height ⟨x,Set.mem_singleton _,rfl⟩ ?_) hs'.2⟩
     exact (hx'.outputs hR.height H (size_path hR hF he hp) ⟨x,hx,rfl⟩ hu.1 hu.2 (fits_path hF hv)).mono (by linarith only)

omit hs hs' hR hF [φ.NeBot]
include H
variable {ε : ℝ} (h : Ticket Z M R U A i p e) [Fintype I] (hU : ∀ x∈ U,∀ i, R i x∈ Ioc (0:ℝ) 1) (hε : 0< ε)
include hU hε h
lemma price : ∃ c>(0:ℝ),∀ t ∈ U,∀ i : Viewers Z, ‖readExpr M.basis (spectator Z i) (e t)‖ ≤ c * p t * surcharges R t ε := by
   let V := Set.prod U (Set.univ : Set (Viewers Z))
   let q(x: W × Viewers Z):= readExpr M.basis (spectator Z x.2) (e x.1)
   obtain ⟨L,hL,h'⟩:= compactify (U:=V) (q:=p ∘ Prod.fst) (fun i=>R i ∘ Prod.fst) q hε (fun x hx i=> hU _ hx.1 i) (fun φ _ T f hf hF=> by
     have hm : Ride R φ T (Prod.fst ∘ f):= ⟨hf.height, hf.entries⟩
     obtain ⟨s,hs',hs⟩:=hm.entries i; obtain ⟨k,hk,hp⟩:=h.wallet hm (fun t=>(hF t).1) hs hs' H
     exact ⟨k,hk,hp.receipt hf.height H hs'.1 hs'.2 (Prod.snd ∘ f)⟩)
   exact ⟨L,hL,fun t ht i=>h' (t,i) ⟨ht,Set.mem_univ i⟩⟩
lemma output_price (w : ℕ) (hx : x ∈ A) (hp : Inspect U (R i) x A) (hm : Window M U w x A) : ∃ c>(0:ℝ),∀ t∈U, ‖M.row (x t) w (e t)‖ ≤ c*(p t*(R i t)^(w:ℝ))*surcharges R t ε := by
   refine compactify R (F:=fun t=> M.row (x t) w (e t)) (q:=fun t=> p t*(R i t)^(w:ℝ)) hε hU ?_
   intro φ _ T f hR hF; obtain ⟨s,hs',hs⟩:= hR.entries i; obtain ⟨k,hk,hV⟩:= h.wallet hR hF hs hs' H; exact ⟨_, hk.mul (hs.rpow (w:ℝ)), RateLE.mono (hV.outputs hR.height H (size_path hR hF hs hp) ⟨x,hx,rfl⟩ hs'.1 hs'.2 (fits_path hF hm)) (by linarith only)⟩
end Ticket
end YM.Contacts.Layers
