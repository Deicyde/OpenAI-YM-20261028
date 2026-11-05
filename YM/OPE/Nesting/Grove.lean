import YM.OPE.Orbits.Kernel

/-!
# Scales of finite separated trees

The root to be expanded has the children (possibly empty) of `.fork`.
Intermediate horizons and ratios will be attached to nonroot `Inner`
vertices. `.Age κ v` uses the current parent's exponent κ at a *leaf*
(input weight in that parent's normalization); it doesn't postulate a new
collapsing radius there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Function Filter Extraction Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

inductive Tree
 | bud
 | fork (n:ℕ)(branch:Fin n→Tree)

namespace Tree

def Leaf : Tree → Type
 | bud => Unit
 | fork _ f => Σ i, (f i).Leaf

def Inner : Tree → Type
 | bud => Empty
 | fork _ f => Unit ⊕ Σ i,(f i).Inner

def Positions : Tree → Type
 | bud => Unit
 | fork _ f => Unit ⊕ Σ i,(f i).Positions

private abbrev leafFt : (t:Tree) → Fintype t.Leaf := Tree.rec (motive:=fun q=>Fintype q.Leaf) (show Fintype bud.Leaf from inferInstanceAs (Fintype Unit)) (fun n f hi=> by
    letI(i:Fin n):Fintype (f i).Leaf:=hi i
    exact inferInstanceAs (Fintype (Σ i,(f i).Leaf)))
instance (t:Tree):Fintype t.Leaf:= leafFt t
private abbrev innerFt : (t:Tree) → Fintype t.Inner := Tree.rec (motive:=fun q=>Fintype q.Inner) (show Fintype bud.Inner from inferInstanceAs (Fintype Empty)) (fun n f hi=> by
    letI(i:Fin n):Fintype (f i).Inner:=hi i
    exact inferInstanceAs (Fintype (Unit⊕ Σ i,(f i).Inner)))
instance (t:Tree):Fintype t.Inner:= innerFt t
private abbrev posFt : (t:Tree) → Fintype t.Positions := Tree.rec (motive:=fun q=>Fintype q.Positions) (show Fintype bud.Positions from inferInstanceAs (Fintype Unit)) (fun n f hi=> by
    letI(i:Fin n):Fintype (f i).Positions:=hi i
    exact inferInstanceAs (Fintype (Unit⊕ Σ i,(f i).Positions)))
instance (t:Tree):Fintype t.Positions:= posFt t

def leafSeat : (t:Tree) → t.Leaf → t.Positions
 | bud,u=> u
 | fork n f,⟨i,j⟩=> .inr ⟨i,(f i).leafSeat j⟩

def topSeat : (t:Tree) → t.Positions | bud=>() | fork _ _ => Sum.inl ()
instance(t:Tree):Inhabited t.Positions:=⟨topSeat t⟩

def topAge : (t:Tree)→ℝ→ (t.Inner→ℝ) → ℝ
 | bud,k,_=>k
 | fork _ _,_,a=> a (Sum.inl ())

@[simp]
theorem age_bud k a: bud.topAge k a=k:=rfl
@[simp]
theorem age_fork {n f k a}: (fork n f).topAge k a=a (Sum.inl ()):=rfl

abbrev childAge {n f}{V:Type}(i:Fin n)(a:(fork n f).Inner→V): (f i).Inner→V:=fun j=> a (Sum.inr ⟨i,j⟩)
abbrev childWages {n f}{V:Type}(i:Fin n)(v:(fork n f).Leaf→V): (f i).Leaf→V:=fun j=>v ⟨i,j⟩
abbrev childPlace {n f}{V:Type}(i:Fin n)(z:(fork n f).Positions→V):(f i).Positions→V := fun j=> z (Sum.inr ⟨i,j⟩)

def cost : (t:Tree)→ℝ→ (t.Inner→ℝ)→(t.Leaf→ℝ) → ℝ
 | bud,k,_,w=> k* (w ())
 | fork n f,_,a,w=> ∑ i, (f i).cost (a (Sum.inl ())) (childAge i a) (childWages i w)
@[simp]
theorem cost_bud k a w: bud.cost k a w = k*(w ()):=rfl
@[simp]
theorem cost_fork {n f k a w}: (fork n f).cost k a w = ∑ i,(f i).cost (a (Sum.inl ())) (childAge i a) (childWages i w):=rfl


def allCap : (t:Tree)→ℝ→(t.Inner→ℝ)→ℝ→Prop := fun _ k a b=> k≤b ∧ ∀ v,a v≤b

def ordered : (t:Tree)→ℝ→ (t.Inner→ℝ)→Prop
 | bud,_,_=>True
 | fork n f,k,a=>k≤a (Sum.inl ()) ∧ ∀ i,(f i).ordered (a (Sum.inl ())) (childAge i a)

def center {L:Type}{t:Tree} (z:L→t.Positions→E4) (s:L) := z s t.topSeat

abbrev Envelope (L:Type)(t:Tree):=L→t.Positions→E4

def down {L n}{f:Fin n→Tree} (i:Fin n)(z:Envelope L (fork n f)):Envelope L (f i):= fun l=> childPlace i (z l)

-- includes actual shrinking also when log time is set by much tinier inner radii than this cluster

def Regular {L:Type}(l:Filter L)(T:L→ℝ): (t:Tree)→ℝ→ (t.Inner→ℝ)→ Envelope L t→Prop
 | bud,k,_,_ => 0≤k
 | fork n f,k,a,z=>
    let α:=a (Sum.inl ()); 0 ≤ k ∧ k ≤ α ∧ enveloped l T α z (center z) ∧
      Tendsto (fun s=>away (z s) (center z s)) l (𝓝 0) ∧
      (∀ i j,i≠j → Intervals l T α (down i z) (down j z)) ∧ ∀ i, Regular l T (f i) α (childAge i a) (down i z)

def Relative (M η:ℝ): (t:Tree)→ (t.Inner→ℝ)→(t.Positions→E4)→Prop
 | bud,_,_=> True
 | fork n f,s,z=> (∀ v, ‖z v-z (fork n f|>.topSeat)‖ ≤ M*s (Sum.inl ())) ∧
   (∀ i j k e, i≠j→ η * s (Sum.inl ()) ≤ ‖childPlace i z k - childPlace j z e‖) ∧
   ∀ i:Fin n, Relative M η (f i) (childAge i s) (childPlace i z)

variable {L:Type}{l:Filter L}{T:L→ℝ}{k B:ℝ}{t:Tree}{a:t.Inner→ℝ}{z:L→t.Positions→E4}

lemma Regular.ageLower (hg:Regular l T t k a z) : k ≤ t.topAge k a:=by cases t with
    | bud=>exact le_rfl
    | fork n f=>exact hg.2.1
lemma Regular.zeroBorder (hg:Regular l T t k a z):0≤k:= by cases t with
    | bud=>exact hg
    | fork=>exact hg.1
lemma Regular.nonneg (hg:Regular l T t k a z):0≤t.topAge k a:= hg.zeroBorder.trans hg.ageLower

variable {n:ℕ}{f:Fin n→Tree}{a:(fork n f).Inner→ℝ}{z:L→(fork n f).Positions→E4}
lemma Regular.buffer (h:Regular l T (fork n f) k a z) : ∀ i j:Fin n, i≠j→ Intervals l T (a (Sum.inl ())) (down i z) (down j z) :=h.2.2.2.2.1
lemma Regular.inside (h:Regular l T (fork n f) k a z) (j:Fin n) : Regular l T (f j) (a (Sum.inl ())) (childAge j a) (down j z) := h.2.2.2.2.2 j
lemma Regular.ageBelow {t:Tree}{a:t.Inner→ℝ} (h':allCap t k a B): t.topAge k a ≤ B:= by cases t with
 | bud=> exact h'.1
 | fork=> exact h'.2 _
lemma Regular.capInside (h':allCap (fork n f) k a B)(j:Fin n): allCap (f j) (a (Sum.inl ())) (childAge j a) B:= ⟨h'.2 _,fun _=>h'.2 _⟩
lemma Regular.extent (hT:Tendsto T l atTop) {t:Tree}{k:ℝ}{a:t.Inner→ℝ}{z:Envelope L t} (h:Regular l T t k a z): enveloped l T (t.topAge k a) z (center z):=by
   cases t with
   | fork n f=>exact h.2.2.1
   | bud=>exact (RateLE.zero l T (-(bud.topAge k a))).congr (Eventually.of_forall fun i=> funext (fun (x:bud.Positions)=> Eq.symm (show z i x-z i ()=0 from by cases x; exact sub_self _))) -- maybe sub_self orientation
lemma Regular.vanish {t:Tree}{a:t.Inner→ℝ}{z:Envelope L t}(h:Regular l T t k a z): Tendsto (fun s=>away (z s) (center z s)) l (𝓝 0):=by
   cases t with
   | fork=>exact h.2.2.2.1
   | bud=>rw [show (fun s=>away (z s) (center z s)) = fun _=>0 from funext fun i=>funext fun (x:Unit)=> by cases x; exact sub_self _]; apply tendsto_const_nhds
end Tree

namespace Measures
variable {L I J I' J':Type}[Fintype I][Fintype J][Fintype I'][Fintype J']{l:Filter L}{T:L→ℝ}{a b:ℝ}{x:L→I→E4}{y:L→J→E4}{o:L→E4}

omit [Fintype I'] [Fintype J'] [Fintype I] [Fintype J] in
lemma interval_comp (h:Intervals l T a x y) (f:I'→I)(g:J'→J): Intervals l T a (fun i=> x i ∘ f) (fun i=>y i ∘ g):=fun c hc=>(h c hc).mono fun s he v w=>he _ _
omit [Fintype I] [Fintype I'] in
lemma kept_comp (h:Kept l T a x)(f:I'→I) (hf:Injective f): Kept l T a (fun i=>x i ∘ f):=by
  intro r hr; exact (h r hr).mono fun s he j k hj=> he _ _ (hf.ne hj)
omit [Fintype I] [Fintype J] [Fintype I'] in
lemma pair_intervals {z:L→I'→E4}(h:Intervals l T a x z)(h':Intervals l T a y z): Intervals l T a (fun i=>beside (x i) (y i)) z:=by
  intro r hr; filter_upwards [h r hr,h' r hr] with i hi hi'
  rintro (s|s) k
  exacts [hi ..,hi' ..]
lemma envelope_comp (h:enveloped l T a x o)(f:I'→I):enveloped l T a (fun i=>x i ∘ f) o := h.transfer (Eventually.of_forall fun i=> (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j=>norm_le_pi_norm (away (x i) (o i)) (f j)))
lemma shrink_comp (h:Tendsto (fun i=>away (x i) (o i)) l (𝓝 0)) (f:I'→I):Tendsto (fun i=>away (x i ∘ f) (o i)) l (𝓝 0):= tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mp h (f j))

lemma kept_sigma {p:I → Type}[∀ i,Fintype (p i)]{m:(i:I)→L→p i→E4} (h:∀ i,Kept l T a (m i))(hs:∀ i j,i≠j → Intervals l T a (m i) (m j)) : Kept l T a (fun s (ij:Σ i,p i)=> m ij.1 s ij.2):= by
    intro b hb
    filter_upwards [eventually_all.mpr (fun i=>h i b hb),eventually_all.mpr (fun i=>eventually_all.mpr (fun j=> eventually_all.mpr (fun hi=>hs i j hi b hb)))] with s hi he
    intro ⟨i,p⟩ ⟨j,q⟩ hh
    by_cases ha:i=j
    · subst j; exact hi i _ _ (fun h'=>hh (congr_arg (Sigma.mk i) h'))
    exact he _ _ ha ..

lemma interval_inject (h:Kept l T b x)(hy:Kept l T b y)(hc: Intervals l T a x y)(hh:a≤b):∀ᶠ i in l,Injective (beside (x i) (y i)):=(h.chorus hy (hc.mono hh)).inject

lemma bounded_interval (hT:Tendsto T l atTop)(hx:Tendsto (fun i=>away (x i) (o i)) l (𝓝 0))(h:∃ c:ℝ, 0<c ∧ ∀ᶠ s in l, OPE.ApartFrom c (sole (o s)) (y s)):Intervals l T 0 x y:=by
     rintro b hb
     obtain ⟨c,hc,h⟩:=h
     have hc':0<c/2:=half_pos hc
     have he:= tendsto_pi_nhds.mp hx
     have h'(j:I):∀ᶠ s in l, ‖x s j-o s‖ < c/2:= (he j).eventually (p:=fun y=>‖y‖ < c/2) (by change _ ∈ 𝓝 (0:E4); convert Metric.ball_mem_nhds (0:E4) hc' using 1; ext v; exact (Metric.mem_ball.trans (by rw [dist_zero_right]; rfl)).symm)
     filter_upwards [eventually_all.mpr h',h, ((RateLE.exp (-b) hT).tends (neg_neg_of_pos hb) hT).eventually (gt_mem_nhds hc')] with i hi h hp
     intro s k
     have hs:= hi s; have hz:=h () k; change c < ‖o i-y i k‖ at hz; change Real.exp _ < c/2 at hp
     linarith only [hp,hs,hz,OPE.c_dist_point (o i) (x i s) (y i k),norm_sub_rev (o i) (x i s)]
end Measures

end YM.OPE.Nesting
