import YM.RG08.Orison.Fort

/-! # Conditioning continuity with regulator-independent cover charges. All scopes at fixed
 horizon & reporting levels; no effective-radius growth claim beyond supplied costs. Ambient
 domain = all t, but use cofinal tails by reindex. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false

def Nice (f:ℕ→ℝ):Prop:=∃ A,∀ i,0≤f i∧ f i≤ A
def hush : Exchange ℕ where
 Good:=Nice
 cheap f:= Nice f ∧ Tendsto f atTop (𝓝 0)
 zero:=⟨⟨0,fun _=>⟨le_rfl,le_rfl⟩⟩,tendsto_const_nhds⟩
 steady r h:=⟨r,fun _=>⟨h,le_rfl⟩⟩
 hear p q hp hq:=by obtain ⟨a,h⟩:=hp;obtain ⟨b,H⟩:=hq; exact ⟨a+b,fun i=>⟨add_nonneg (h i).1 (H i).1,add_le_add (h i).2 (H i).2⟩⟩
 moreover p q hp hq:=by obtain ⟨a,h⟩:=hp;obtain ⟨b,H⟩:=hq; exact ⟨a*b,fun i=>⟨mul_nonneg (h i).1 (H i).1,mul_le_mul (h i).2 (H i).2 (H i).1 ((h i).1.trans (h i).2)⟩⟩
 lasts p q hp hq:=by
    obtain ⟨⟨a,h⟩,ha⟩:=hp;obtain ⟨⟨b,H⟩,hb⟩:=hq
    exact ⟨⟨a+b,fun i=>⟨add_nonneg (h i).1 (H i).1,add_le_add (h i).2 (H i).2⟩⟩, by simpa using! ha.add hb⟩
 awe p q hp hq:=by
    obtain ⟨a,h⟩:=hp;obtain ⟨⟨b,H⟩,hb⟩:=hq
    refine ⟨⟨a*b,fun i=>⟨mul_nonneg (h i).1 (H i).1,mul_le_mul (h i).2 (H i).2 (H i).1 ((h i).1.trans (h i).2)⟩⟩,?_⟩
    apply squeeze_zero (fun i=>mul_nonneg (h i).1 (H i).1) (fun i=>mul_le_mul_of_nonneg_right (h i).2 (H i).1)
    simpa using hb.const_mul a
 safe p hp i:=by obtain ⟨p,h⟩:=hp;exact (h i).1
 hale p q hp h he:=by obtain ⟨a,H⟩:=hp;exact ⟨a,fun i=> ⟨h i,(he i).trans (H i).2⟩⟩
 nope p hp:=hp.1
 hat p q hp h he:=by obtain ⟨⟨a,H⟩,hx⟩:=hp;exact ⟨⟨a,fun i=>⟨h i,(he i).trans (H i).2⟩⟩,squeeze_zero h he hx⟩

lemma nicety {p:ℕ→ℝ}(h:Tendsto p atTop (𝓝 0))(hp:∀ i,0 ≤ p i):hush.cheap p:=by
 have ht : Bornology.IsBounded (Set.range p):= Metric.isBounded_range_of_tendsto p h
 obtain ⟨B,hB⟩:= ht.bddAbove
 exact ⟨⟨B,fun i=>⟨hp i,hB (Set.mem_range_self i)⟩⟩,h⟩

variable {I:Type} {n:ℕ}
/-- fixed level joint recipe price on analytic stencil family at every N, including comparison
 to a REGULATOR-FREE tensor. -/
def Tone (F:ℕ→Flake n (Market I))(V:Flake n (Market I))(σ:ℝ):Prop:=∃ δ:ℕ→ℝ,hush.cheap δ∧ Lance (I:=fun _=>I) hush (fun _=>σ) δ F fun _=> V
variable {F A:ℕ→Flake n (Market I)}{V B:Flake n (Market I)}{σ σ' :ℝ}
lemma Tone.field (h:Tone F V σ)(he:0<n)(hs:0≤σ):∀ t,Tendsto (fun i=>F i t) atTop (𝓝 (V t)):=by
 obtain ⟨d,hd,h⟩:=h;obtain ⟨p,hp,H⟩:=h.berry hd; intro t
 rw [tendsto_iff_norm_sub_tendsto_zero]
 exact squeeze_zero (fun i=>norm_nonneg _) (fun i=>by rw [Real.norm_eq_abs];exact (H i).plain (tiny _ hp _) hs he t) (show Nice p ∧ _ from hp).2
lemma Tone.narrow (h:Tone F V σ)(he:σ' ≤ σ):Tone F V σ':=by obtain ⟨d,hx,h⟩:=h;exact ⟨_,hx,h.vow (fun _=>le_rfl) (fun _=>he)⟩
lemma Tone.add (h:Tone F V σ)(ht:Tone A B σ): Tone (fun i=>F i+A i) (V+B) σ:=by
 obtain ⟨p,hp,H⟩:=h;obtain ⟨q,hq,H'⟩:=ht;have he:=hush.lasts _ _ hp hq;refine ⟨_,he,Lance.add (H.vow (fun x=>le_add_of_nonneg_right (tiny _ hq _)) (fun _=>le_rfl)) (H'.vow (fun x=> le_add_of_nonneg_left (tiny _ hp _)) (fun _=>le_rfl)) (tiny _ he)⟩
lemma Tone.neg (h:Tone F V σ):Tone (fun i=> - F i) (-V) σ:=by obtain ⟨p,hp,H⟩:=h;exact ⟨_,hp,H.opposite⟩
lemma Tone.sub (h:Tone F V σ)(ht:Tone A B σ):Tone (fun i=> F i-A i) (V-B) σ:=by simpa only [sub_eq_add_neg] using h.add ht.neg
lemma nil : Tone (fun _:ℕ=>0:ℕ→Flake n (Market I)) 0 σ:=⟨_,hush.zero,Ducat.zero hush _ _⟩
lemma Tone.series {J:Type}(s:Finset J){F:J→ℕ→Flake n (Market I)}{A:J→Flake n (Market I)}(h:∀ i∈s,Tone (F i) (A i) σ):Tone (fun k=>∑ i∈s,F i k) (∑ i∈s,A i) σ:=by
 induction s using Finset.induction_on with
 | empty=>simpa only [sum_empty] using (@Orison.nil I n σ)
 | insert a s ha hi=>simpa only [sum_insert ha] using ((h a (mem_insert_self ..)).add (hi (fun i hi=>h _ (mem_insert_of_mem hi))))
-- convert emissions to Tone using N reindex. no need assert a tone when outside quota, as retreat can choose zero pad.
lemma sounds (F:ℕ→Flake n (Market I))(σ p:ℝ)(A:ℕ→ℝ)(k m:ℕ)(hk:k ≤ m)(h:Sums σ F A p k)(ht:Tendsto A atTop (𝓝 0))(hs:0≤p)(he:∀ i,k ≤ i →0≤ A i)(hh:∀ i,k ≤ i → Held (carpet _) σ p (F i)): Tone (fun i=>F (i+m)) (hope F) σ:=by
 apply grazing (I:=fun _:ℕ=>I) (show Bound hush (fun _=>σ) (fun i=>F (i+m)) from ⟨_,hush.steady _ hs,fun i=>hh _ (by omega)⟩) (show Bound hush _ _ from ⟨_,hush.steady _ hs,fun _=>h.2.1⟩)
 exact ⟨_,nicety ((tendsto_add_atTop_iff_nat _).2 ht) (fun i=>he (i+m) (by omega)),fun _=>h.2.2 _ (by omega)⟩
end YM.RG08.Orison
