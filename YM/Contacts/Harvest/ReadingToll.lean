import YM.Contacts.Harvest.Reader
/-! # Toll a reader on every log-path

Affordability of the *repeated* linear operations required when testing at the next scale.
No assumption is made that the argument already has only the leading power; this tests on
inputs estimated in the same hierarchy before taking limits. Apply even on several simultaneous
shrinking paths. This is power counting at fixed number of projections and fixed field labels,
not enough control for all PT orders.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Submodule Table Spec OPE Normal MultipleContact Layers
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} {Z : Final C F S}
variable {M : Devices Z.sector.derivatives}
variable {E W I X : Type} {k : ℕ}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {g : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k}[NormedAddCommGroup X][NormedSpace ℂ X]
local notation "GN" => Normal.Group k
namespace Route
variable (r : Route P Q I W) {D : Reader E W X k Z.sector.derivatives}
variable {φ : Filter ℕ} {T : ℕ→ℝ} {w : ℕ→W} {x y : ℕ→ E} {s t c : ℝ}
-- fixed layer, on all admissible paths. Don't need compactness of schedules.
def avenue (j : Normal.Group k)(w : ℕ→ W)(x : ℕ→ E) := Set.range fun i:Nails j=>fun t:ℕ=> r.oculus (w t) i.val (x t)
lemma along_paths (i : Q.parts)(w x): (fun t=> r.oculus (w t) i.val (x t)) ∈ r.avenue i.val w x:= ⟨⟨i.val,by rfl,Q.nonempty_of_mem_parts i.property⟩,rfl⟩
lemma avenue_other {i j : GN} (w) (hx : ∀ t,x t-y t∈ normalOn P i)(h : Disjoint j i) : r.avenue j w x ⊆ r.avenue j w y := by rintro p ⟨c,rfl⟩; exact ⟨c,funext fun t=> (r.oculus_still (w t) c.val (x t) (y t) (hx t) (.inr (Disjoint.mono_right c.property.1 h.symm))).symm⟩
lemma avenue_inherits {i j : GN} (h : j ⊆ i)(w x) : r.avenue j w x⊆ r.avenue i w x:= by rintro p ⟨c,rfl⟩; exact ⟨⟨c.val,Finset.Subset.trans c.property.1 h,c.property.2⟩,rfl⟩

abbrev Entry (φ : Filter ℕ) (T u : ℕ→ℝ) (t : ℝ) := t∈ Icc (0:ℝ) 1 ∧ RateIs φ T u (-t)
lemma RateEqual [φ.NeBot] {f : ℕ→ℝ} (h : RateIs φ T f c) (k : RateIs φ T f s) : c=s:= tendsto_nhds_unique h.rate k.rate
lemma Entry.same [φ.NeBot] {f : ℕ→ℝ}(h : Entry φ T f t)(k : Entry φ T f s) : t=s:= neg_injective (RateEqual h.2 k.2)

def booked (Z:Final C F S) (M : Devices Z.sector.derivatives) (c : ℝ) (φ : Filter ℕ) (T : ℕ→ℝ) (w : ℕ→W)(x : ℕ→ E)(i : Normal.Group k) (e : ℕ→ Expression Z.sector.derivatives) :=
  ∀ t:ℝ,Entry φ T (r.R i ∘ w) t → Funds Z M φ T (r.avenue i w x) t c e

structure Loan (Z:Final C F S)(M : Devices Z.sector.derivatives)(r : Route P Q I W)(B : W → ℝ) (D : Reader E W X k Z.sector.derivatives) : Prop extends Lit r D where
   currency : Bill r.diameter univ B
   path {φ : Filter ℕ} [φ.NeBot] {T : ℕ→ℝ}{w : ℕ→ W}{x : ℕ→ E}{b : ℝ} (hp : Ride r.diameter φ T w)(hb: RateIs φ T (B ∘ w) b)(hA : ∀ i,x i∈ r.stage (w i))
      (c : Normal.Group k →ℝ) (e : Normal.Group k → ℕ→ Expression Z.sector.derivatives)(he : ∀ i∈Q.parts,r.booked Z M (c i) φ T w x i (e i)): RateLE φ T (fun i=> D (w i) (x i) (∏ j∈ Q.parts,tag j (e j i))) (b+ (Q.parts.sum c))

-- spatial powers bookkeeping uses common gain from K+1, or from output weight in the tail.
def gain {d : Fin k→ℕ}{i : Normal.Group k} (v : Way d i) := v.elim (levels d i) Fin.val
lemma gain_live (d : Fin k→ℕ)(i : GN) : gain (none: Way d i)=levels d i:= rfl
lemma gain_project {d : Fin k→ℕ}{i : GN} (w : Fin (levels d i)) : gain (d:=d) (i:=i) (some w) = w.val := rfl

def raises (p : ℝ)(t u : ℝ)(v : ℕ) := p*(t/u)^(v:ℝ)
def promise (i : Q.parts){d:Fin k→ℕ}(q : Way d i.val) (u:Fans P i.val)(v:Splittings i.val)(B : W→ℝ)(p : r.ramp i (outward q) u v):= raises (B p.val.1) p.val.2 (r.R i.val p.val.1) (gain q)
lemma charging {f u v : ℕ→ℝ}{p s t : ℝ}(hf : RateIs φ T f p)(hu : RateIs φ T u (-s))(hv : RateIs φ T v (-t))(i : ℕ) : RateIs φ T (fun j=> raises (f j) (u j) (v j) i) (p+(t-s)*i) := (hf.mul ((hu.div hv).rpow (i:ℝ))).swap (by ring)

variable (i : Q.parts)
variable {d : Fin k→ℕ} {A : ℕ→ℝ} (u : Fans P i.val)(v : Splittings i.val)
lemma crossroads (hR : RateIs φ T A (-s)) (hT : Tendsto T φ atTop) (ha : ∀ j, 0<A j) (hx : ∀ t,x t∈ u.patch v (A t)) : (v.val.parts:Set GN).Pairwise (fun l p=> Cross φ T s (r.avenue l w x) (r.avenue p w x)):= by
   rintro l hl p hp he f ⟨f,rfl⟩ g ⟨g,rfl⟩
   obtain ⟨C,hc,h⟩:= u.through (r.displaysNormals i.val i.property) v ⟨l,hl⟩ ⟨p,hp⟩ (fun h=>he (congr_arg Subtype.val h)) f g
   refine from_gap hR hT C hc (Eventually.of_forall fun j=>?_); change C*A j ≤ ‖r.oculus _ f.val (x j)-r.oculus _ g.val (x j)‖
   rw [show r.oculus _ f.val _-r.oculus _ g.val _ = _ from r.oculus_diff (w j) (x j) i ⟨f.val, Finset.Subset.trans f.property.1 (v.val.le hl),f.property.2⟩ ⟨g.val,Finset.Subset.trans g.property.1 (v.val.le hp),g.property.2⟩]; exact h (ha j) _ (hx j)
lemma combines_funds (B : GN→ ℝ)(E : GN→ ℕ→ Expression Z.sector.derivatives)(hT : Tendsto T φ atTop)(hR : Entry φ T A s)(ha : ∀ j, 0<A j)(hx : ∀ j,x j∈ u.patch v (A j))(hE : ∀ j∈ v.val.parts, Funds Z M φ T (r.avenue j w x) s (B j) (E j)): Funds Z M φ T (r.avenue i.val w x) s (∑ j∈ v.val.parts, B j) (fun t=> ∏ j∈ v.val.parts,E j t):= by
   have he:= Funds.product hT hR.1.2 hE (r.crossroads i u v hR.2 hT ha hx); apply Funds.ident (Funds.mono he le_rfl (iUnion₂_subset fun j hj=> r.avenue_inherits (v.val.le hj) w x)); exact Eventually.of_forall fun i=> Finset.prod_apply ..
variable (b : Way d i.val)
-- splitting out `Fw` lets parent read beyond U iff *projected*
lemma spent {A : ℕ→ℝ} (e : ℕ→ Expression Z.sector.derivatives) (hs : Services C F S)(h : r.Authority M d)(hb : ∀ j,x j∈r.site i (outward b) u v (w j) (A j)) (hK : ∀ j,x j-y j∈ normalOn P i.val)(he : outward b=false → x=y)
   (hT : Tendsto T φ atTop)[φ.NeBot] (_ha : ∀ j, 0<A j)(hA : Entry φ T A s)(hx : Funds Z M φ T (r.avenue i.val w x) s c e)(hm : Entry φ T (r.R i.val ∘ w) t) : Funds Z M φ T (r.avenue i.val w y) t (c+(t-s)*gain b)
         (fun j=> wind M d i.val b (r.oculus (w j) i.val (x j)) (e j)) := by
   let f(j):= r.oculus (w j) i.val (x j)
   have heL : Habitat φ T s f (r.avenue i.val w x):= by
      rintro p ⟨g,rfl⟩; exact from_span hA.2 hT 2 (Eventually.of_forall fun j=> le_trans (r.oculus_extent (w j) (x j) i g) ((hb j).2.1.2))
   have hc(j:Fin (levels d i.val)) : Fits M φ j.val f (r.avenue i.val w x):= by
      rintro g ⟨g,rfl⟩; exact Eventually.of_forall fun j'=> (r.oculus_extent (w j') (x j') i g).trans (le_trans (r.horizon i _ _ _ _ _ (hb j')) (r.clearance_through h i.val j.isLt))
   have hf:f ∈ r.avenue i.val w x := r.along_paths i w x
   cases b with
   | none =>
      obtain rfl:= he rfl; have hm':t ≤ s:= tighter hT hA.2 hm.2 (2*r.reserve) (Eventually.of_forall fun j=> r.active i u v _ _ ⟨_,hb j⟩)
      rw [gain_live]; by_cases hh:levels d i.val=0
      · simp_rw [straight M d i.val hh]; rw [hh]; simpa only [LinearMap.id_coe,id_eq,Nat.cast_zero,mul_zero,add_zero] using! hx.coarsen hT hs heL hf hm' hA.1.2 hm.1.1
      let n:= levels d i.val-1; have hh':levels d i.val=n+1:= by omega
      simp_rw [turned M i.val _ (w:=n) hh']; rw [hh']; let g:= e-statedProject M n f e; have ht:= hx.drop hT hs heL hf (hc (⟨n,hh'.symm ▸ Nat.lt_succ_self n⟩: Fin (levels d i.val))) hm' hA.1.2 hm.1.1; exact ht.mono (le_of_eq (by push_cast; ring)) (by rfl)
   | some v=>
      have ht:=hx.outputs hT hs heL hf hA.1.1 hA.1.2 (hc v); rw [gain_project]; change Funds Z M φ T _ t _ (fun j=> insertField M.basis (f j) _ (M.row (f j) v _));
      refine (Fine.field hT (x:=f) (?_) (ht.mono (le_of_eq (by ring)))).funds hm.1.2; rw [show f=(fun j=> r.oculus (w j) i.val (y j)) from funext fun j=> r.oculus_still (w j) i.val (x j) (y j) (hK j) (Or.inl rfl)]; exact r.along_paths i w y

lemma forks (b' : Bool) (h : 1 < i.val.card)(f : ℕ → r.ramp i b' u v)(he : Ride (r.renew i b' u v h).diameter φ T f) : Ride r.diameter φ T (fun i=> (f i).val.1) := ⟨he.height,fun j=> he.entries (some j)⟩
lemma fresh_bill {B:W→ℝ}(h : 1 < i.val.card) (hg : Bill r.diameter univ B) : Bill (r.renew i (outward b) u v h).diameter univ (r.promise i b u v B) := by
   constructor
   · intro x hx; exact mul_pos (hg.pos _ (Set.mem_univ _)) (Real.rpow_pos_of_pos (div_pos x.property.1.1 (r.valid _ _ |>.1)) _)
   intro φ _ T x hu ht
   have hh:= r.forks i u v (outward b) h x hu; obtain ⟨k,hk⟩:=hg.exactRate φ T _ hh (fun i=>Set.mem_univ _); obtain ⟨c,hc,hv⟩:= hu.entries none; obtain ⟨t,ht,hA⟩:= hh.entries (r.register i.val); exact ⟨_, charging hk hv hA (gain b)⟩
lemma loan_listens (A : Services C F S){B : W→ℝ}(hm:Loan Z M r B D)(h : 1 < i.val.card)(he : r.Authority M d) : Loan Z M (r.renew i (outward b) u v h) (r.promise i b u v B) (r.listener M i b u v D):= by
   let E':= Expression Z.sector.derivatives; let q:= replace i v.val; let r':= r.renew i (outward b) u v h
   refine ⟨r.listener_plot hm.toLit i b u v he h,r.fresh_bill i u v b h hm.currency,?_⟩
   intro φ hN T w x c hW hc ht d' e he'
   let y j:= (w j).val.1; let a j:= (w j).val.2; have hp:= r.forks i u v (outward b) h w hW; have hw (j): x j ∈ r.site i (outward b) u v (y j) (a j):=ht j
   obtain ⟨s,hs,hh⟩:= hW.entries none; have hE : Entry φ T a s:=⟨hs,hh⟩; obtain ⟨t,H,h'⟩:= hp.entries (r.register i.val); have ht' : Entry φ T (r.R i.val ∘ y) t:=⟨H,h'⟩; obtain ⟨k,hk⟩:= hm.currency.exactRate φ T y hp (fun t=>Set.mem_univ _)
   have hr : c=k+(t-s)*gain b:= RateEqual hc (charging hk hE.2 ht'.2 (gain b));
   choose z hz hA hF using fun j=> follows _ (hw j|>.1); have hz': ∀ j, z j∈ r.stage (y j):= hz
   let f(j:ℕ):= wind M d i.val b (r.oculus (y j) i.val (x j)) (∏ k∈v.val.parts,e k j); let e':= Function.update e i.val f; let B':= Function.update d' i.val (v.val.parts.sum d'+(t-s)*gain b)
   have hQ:=r.combines_funds i u v d' e hp.height hE (fun j=> (w j).property.1.1) (fun j=> (r.sun_shade i _ _ _ _ _ (hw j))) (fun j (hj:j∈v.val.parts)=> (?_ : Funds Z M φ T (r.avenue j y x) s (d' j) (e j)))
   swap
   · apply he' j (by rw [replace_parts]; exact Finset.mem_union_right _ hj) s; change Entry φ T (r'.R j ∘ w) s; rw [show (r'.R j ∘ w)=a from funext fun x=> r.R_here i (outward b) u v h hj _]; exact hE
   have hk':= hm.path hp hk hz' B' e' (fun j hj=> (?_))
   swap
   · by_cases hx:j=i.val
     · subst j; intro u' he'; have he'' : u'=t:= Entry.same he' ht'; subst u'; change Funds _ _ _ _ _ _ (B' i.val) (e' i.val); simp_rw [B',e',Function.update_self]; exact r.spent i u v b _ A he hw hA (fun h=> funext fun j=> (hF j).resolve_right (fun h'=> by rw [h'] at h; contradiction)) hp.height (fun j=>(w j).property.1.1) hE hQ ht'
     intro u' he''; have hu:j∈ Q.parts.erase i.val := Finset.mem_erase.mpr ⟨hx,hj⟩; have ht:= he' j (by rw [replace_parts]; exact Finset.mem_union_left _ hu) u' (by rw [show ((r.renew i (outward b) u v h).R j ∘ w)=r.R j ∘ y from funext fun a=> r.R_there i (outward b) u v h (Finset.disjoint_left.mp (replace_disj i v.val) hu) _]; exact he''); simp_rw [e',B',Function.update_of_ne hx]; exact ht.mono le_rfl (r.avenue_other y hA (Q.disjoint hj i.property hx))
   apply RateLE.congr (F:=fun j=> D (y j) (z j) (∏ k∈Q.parts,tag k (e' k j))) ?_ (Eventually.of_forall fun j=>?_)
   · apply hk'.mono; rw [hr,replace_parts,Finset.sum_union (replace_disj i v.val),← Finset.sum_erase_add Q.parts B' i.property, show (Q.parts.erase i.val).sum B'= (Q.parts.erase i.val).sum d' from Finset.sum_congr rfl (fun j hj=> Function.update_of_ne (Finset.mem_erase.mp hj).1 ..), show B' i.val=_ from Function.update_self i.val (v.val.parts.sum d'+(t-s)*gain b) d']; linarith only
   change _= D (y j) (x j) (System.review Q i v.val _ (∏ k∈(replace i v.val).parts,tag k (e k j))); rw [hm.keeps (y j) i (hA j),weld_factors i v.val (wind M d i.val b (r.oculus (y j) i.val (x j))) (fun k=> e k j)] -- motive
   apply congrArg (D _ _); refine Finset.prod_congr rfl fun k hk=>?_ ; by_cases he:k=i.val; · subst k; simp [e',Function.update_self,f]
   simp only [e',Function.update_of_ne he]
end Route
end YM.Contacts.Harvest
