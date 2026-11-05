import YM.Contacts.Solstice.Legal
/-!
# Well-definedness of the detector readings on their apertures

At end of the recursion after decomposing into the canonical sums and annular pairings the value
of the extensions has **not** used any readings on overlarge/overlapping/junk words. Use only on
the given domain of `𝓓` tests (distributions and root formulas mean this below). No assertion of
convergence of an extension of the *separated kernels without the Taylor prescription*. Here use
pointwise germs of tests at all stages, no modification of the transport of Fields at any finite
branch/path.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X]
variable {k : ℕ}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{Z:Final C F S}
variable {g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g}{d : Fin k→ℕ}
local notation "E!"=> Expression Z.sector.derivatives
local notation "GN"=> Normal.Group k

namespace Mirror
variable (M:Devices Z.sector.derivatives)(r:Route P Q I W)(T:W→ Cells S d)(H:Reader E W X k Z.sector.derivatives)(Y:Mirror Z)
variable (f:Menu k)(w:W)(p:SmoothTests E)(i:Q.parts)(b:Way d i.val)
def story := scoreAt H w p ((tailor M r T Y w).election P (r.length w) f Q)
def undertake := scoreAt H w p ((tailor M r T Y w).absentee P (r.length w) f Q i (fun x=> footprint Y (r.oculus w i.val x) b))
lemma telling (h : 1 < i.val.card) (x : E) : story M r T H Y f w p x=
     ∑ b∈ (r.components M T w).slate i.val (f i.val), undertake M r T H Y f w (System.sliceAt P i.val (f i.val).slice (r.net i (d:=d) b w p)) i (d:=d) b x:= by
   unfold story scoreAt; rw [System.renewal _ _ _ _ _ i h,map_sum]; let L:Finset (Way d i.val):= (r.components M T w).slate i.val (f i.val)
   apply Finset.sum_congr (show (tailor M r T Y w).slate i.val (f i.val)= L from rfl); intro b hb; unfold undertake scoreAt; let b':Way d i.val:=b
   rw [show (tailor M r T Y w).treatment i.val b=(fun x=> footprint Y (r.oculus w i.val x) b') from funext fun x=> loom M r T Y i.val w x b', show (tailor M r T Y w).maskAt P (r.length w) i.val b=r.net i b' w from by cases b <;> rfl]

lemma undertake_range {J: Type*} (K:Finset J) (z:J→SmoothTests E)(x:E): undertake M r T H Y f w (∑ j∈K,z j) i b x= ∑ j∈K,undertake M r T H Y f w (z j) i b x:= map_sum ((H w x).comp (Normal.under x _)) z K

-- as algebra
private def Card (A:Type)[CommRing A][Algebra ℂ A] (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] : (E→A)→ₐ[ℂ] Score E A:= Algebra.TensorProduct.includeLeft
private def aloneField (j:GN)(x:E) := ∏ k∈ j,(r.components M T w).field k x
private def leaf (x:E):=H w x (∏ j∈Q.parts,tag j (aloneField M r T w j x))
lemma leaf_rules (K:System E E! k)(h : ∀ i∈Q.parts,i.card≤1)(hk : K.field=(r.components M T w).field)(x:E) : scoreAt H w p (K.election P (r.length w) f Q) x= p.val x • leaf M r T H w x:= by
   -- adapt Lined
   let t(j:GN)(x:E):= tag j (aloneField M r T w j x); let R:= K.present P (r.length w) f; let L':= Board GN (Letter Z.sector.derivatives)
   have he:product Q.parts R=product Q.parts (fun i=> Card L' E (t i)):= by
      apply eq_product; intro i hi; obtain ⟨j,rfl⟩:=alone_in h hi; unfold R System.present; rw [K.alone P (r.length w) {j} _ (h _ hi), K.full_single,retags, reshape_tape]; change evaluateHeads (fun (_:E)=> (tag ({j}:GN)).toLinearMap) (K.field j) ⊗ₜ[ℂ] (1:Optical E)= t {j} ⊗ₜ[ℂ] _; rw [hk]; congr; funext x; simp [t,aloneField,evaluates]
   have hx : scoreAt H w p (K.election P (r.length w) f Q) x= H w x (action x p (product Q.parts R)):= rfl
   rw [hx,he,← show Card L' E (product Q.parts t)=product Q.parts (fun i=> Card L' E (t i)) from mapped _ t (Card L' E).toRingHom, product_true]; change H w x (action x p ((∏ i∈Q.parts,t i) ⊗ₜ[ℂ] (1:Optical E)))=_; rw [action_tmul, Finset.prod_apply,map_smul]; rfl

variable {Y M r H} {D : Reader E W X k Z.sector.derivatives}
lemma vacants (h : ∀ i∈Q.parts,i.card≤1)(hp:tsupport p.val⊆r.stage w)(hh : Mirrors Z r H D)(x:E) : r.windings M H T f w p x= story M r T D Y f w p x:= by
    unfold story windings; rw [leaf_rules M r T D f w p (tailor M r T Y w) h rfl,leaf_rules M r T H f w p _ h rfl]; by_cases hx:p.val x=0; rw [hx,zero_smul,zero_smul];
    congr 1; refine hh.tested _ _ (hp (subset_closure hx)) (fun j=>aloneField M r T w j x) ?_; intro j hj; obtain ⟨a,rfl⟩:= alone_in h hj; unfold aloneField; rw [Finset.prod_singleton,r.core_field]; apply Displays.field (fun _ _=> show _ from ( ?_ : r.actualAt w x a∈r.palette w {a} x)) continuousOn_const continuousOn_const
    exact ⟨⟨{a},by rfl,Finset.singleton_nonempty a⟩, centroid_single ..⟩

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
-- inductive hypothesis class. no need estimates in this theorem

def indemnity (M:Devices Z.sector.derivatives)(r : Route P Q I W) (H D:Reader E W X k Z.sector.derivatives) (T : W→ Cells S d) (Y : Mirror Z): Prop := ∀ (f:Menu k) (w) (p:SmoothTests E), tsupport p.val⊆r.stage w → r.windings M H T f w p =ᵐ[volume] story M r T D Y f w p
omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma dark_lengths (hp : tsupport p.val⊆r.stage w) (u : Fans P i.val) (h : 1 < i.val.card)
     (hy : ∀ v:Splittings i.val, indemnity M (r.renew i (outward b) u v h) (r.listener M i b u v H) (ask r Y i u v b D) (fun t:r.ramp i (outward b) u v=>T t.val.1) Y) (n : ℕ):
  r.beckon M T H i b f w p n =ᵐ[volume] undertake M r T D Y f w (mask (eclipse (normalOn P i.val) (dyad n)) (r.net i b w p)) i b:=by
   let K:= normalOn P i.val; let q(v:Splittings i.val):= r.target i b u v w p (dyad n)
   have he (v:Splittings i.val) : r.hail M T H i b u v f w p (dyad n)=ᵐ[volume] undertake M r T D Y f w (q v) i b:= by
      by_cases hc:(r.site i (outward b) u v w (dyad n)).Nonempty; swap
      · have hh:= r.no_target i b u v (dyad_pos n) hp hc; apply Eventually.of_forall; intro x; change r.select M T H i b f w (q v) x=_; rw [show q v=0 from hh,r.selected_nil]; unfold undertake scoreAt; change (0:X)= D w x (Normal.under x _ 0); rw [map_zero,map_zero]
      let L:r.ramp i (outward b) u v:=⟨(w,dyad n),⟨dyad_pos n,dyad_le n⟩,hc⟩; let S:=tailor M r T Y w; let l(v':E):=footprint Y (r.oculus w i.val v') b; have hx : tsupport (q v).val ⊆ r.site i (outward b) u v w (dyad n):= r.targets i b u v (dyad_pos _) hp; filter_upwards [hy v (widenMenu v f) L (q v) hx] with x hw; rw [show r.hail M T H i b u v f w p (dyad n) x=_ from r.held M T H i b u v h f p L hp x,hw]; apply congrArg (D w x); symm; exact S.in_splitting P _ f Q i v (r.displaysNormals i.val i.property) (q v) (hx.trans ((r.sun_shade ..).trans (u.lights (r.displaysNormals i.val i.property) v (dyad_pos _)))) l x
   filter_upwards [eventually_all.mpr he] with x hx; rw [r.splitted M T H i b u f w p n x, ← u.ray_sums _ (dyad_pos n), undertake_range]; exact Finset.sum_congr rfl fun i _=> hx i

lemma assembles (hp : tsupport p.val⊆r.stage w) (h : ∀ n : ℕ,r.beckon M T H i b f w p n =ᵐ[volume] undertake M r T D Y f w (mask (eclipse (normalOn P i.val) (dyad n)) (r.net i b w p)) i b) :
      let F:= System.sliceAt P i.val (f i.val).slice (r.net i b w p); r.select M T H i b f w F=ᵐ[volume] undertake M r T D Y f w F i b := by
   generalize he:(f i.val).slice = s'; cases s' with
   | some n=>exact h n
   | none =>
      let q:= r.net i b w p; let K:=normalOn P i.val; let V(j:ℕ):= mask (eclipse K (dyad j)) q
      have ht : ∀ᵐ x:E,∀ᶠ n in (atTop:Filter ℕ), (∑ j∈Finset.range n,undertake M r T D Y f w (V j) i b x)=undertake M r T D Y f w q i b x:= by
         filter_upwards [(tailor M r T Y w).announces P (r.length w) Q i f (r.displaysNormals i.val i.property) (fun x=> footprint Y (r.oculus w i.val x) b) (h:=fun x hx=> reunion K q (r.halo_small i b hp) hx)] with x hx; filter_upwards [hx] with n hn; rw [← undertake_range]; exact congrArg (D w x) hn
      filter_upwards [ae_all_iff.mpr h,ht,r.emerges M T H i b hp f] with x hw ht hx; change r.select _ _ _ i b f w q x = undertake _ _ _ _ _ _ _ q _ _ _; obtain ⟨i,ht,he⟩ := (ht.and hx).exists; exact he.symm.trans ((Finset.sum_congr rfl fun i _=> hw i).trans ht)

lemma promised (hm:r.Authority M d)(he:Y.Consent M)(h: Mirrors Z r H D) : indemnity M r H D T Y := by
   suffices hv : ∀ n:ℕ, g.card-Q.parts.card=n → indemnity M r H D T Y from hv _ rfl
   intro n hk; induction n using Nat.strong_induction_on generalizing W I Q with
   | h n ih=>
     intro f w p hp; by_cases hq:∀i∈Q.parts,i.card≤1; exact Eventually.of_forall fun x=> vacants T f w p hq hp h x
     push Not at hq; obtain ⟨i,hi,hh⟩:=hq; let j:Q.parts:=⟨i,hi⟩; have hs:1< j.val.card:=hh; let u:Fans P j.val:= Classical.choice (available_fans P (r.displaysNormals _ hi) (Q.nonempty_of_mem_parts hi));
     have heL(b:Way d j.val):= assembles (Y:=Y) T f w p j b hp (fun a=> dark_lengths T f w p j b hp u hs (H:=H) (D:=D) (fun v=> by
       let k':= (replace j v.val).parts.card; let q:= r.renew j (outward b) u v hs; have ht : g.card-k' < n:= by have hh : Q.parts.card < k':= replace_finer j v.property; have he:= (replace j v.val).card_parts_le_card; omega; --
       exact ih _ ht _ (show q.Authority M d from hm) (mirrors_front j u v b hs hm h he) rfl ) a)
     filter_upwards [(eventually_all).mpr heL] with x hx; rw [r.decomposition M T H j hs,telling _ _ _ _ _ _ _ _ j hs]; exact Finset.sum_congr rfl fun i _=> hx i
end Mirror
end YM.Contacts.Solstice
