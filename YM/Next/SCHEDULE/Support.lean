import YM.Corona.Spend
import YM.Next.SCHEDULE.Pre

/-!
# Pre-L support exchange rate

eq:Fproj, eq:ageom, eq:1shape. Use with complete projected
supports incl all data dependence. Importantly pointwise (independent of period
and *all* supports), anchored→hit for the actual SumBudget test. Separate
assertion that formula data can be localized into these supports NOT made.

Native site max-distance and `coverNumber` of connected cover on actual torus
(include all projected unions, windows, correlations and flag reads when using
this). There's no wrap hypothesis nor measure normalization or supremum almost
sure convention. Don't do this with a quoted bound on path *kernel location*
instead of path length; on original complete E,K supports already all sites
count. The exp estimate is independent of path multiplicity. This buys arbitrary
finite support-exponent shifts *chosen pre-L* on each transition, incl j→j
without spending any of the exponent needed at an earlier scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Lattice Filter RG RG.Supply Bid Precision Function Finset
open scoped Topology BigOperators

variable {G : Gauge} {s : Survey G} {q : Quote} {e : Exchange} {j i : ℕ}
variable {c f n : Side}

def foundation (s : Survey G) (e : Exchange) (j : ℕ) := min (s.o.A j) e.guard
def payment (s : Survey G) (e : Exchange) (j : ℕ) := e.foot*(s.o.A j+e.extra)

lemma foundation_pos (s : Survey G) (e : Exchange) (j : ℕ) : 0 < foundation s e j := lt_min (s.o.pos j) e.ok.2.1

/-- Require a pre-L halo estimate on projected *complete* supports. -/
def Footage (l : Ratio c f) (r B : ℕ) (X : Support f) (Y : Support c) :=
    Y ⊆ halo (r*B) (X.image l.parent)

lemma Buy.footage (l : Ratio c f) (h : Buy s q e j i l.count.val)
    (a b : ℝ) (ha : foundation s e j ≤ a) (hb : 0 ≤ b) (he : b ≤ s.o.A j+e.extra)
    {M B : ℕ} (hg : 0 < B) (hh : M ≤ 2*B) (X : Support f) (Y : Support c) (ht : Footage l e.radius B X Y) :
    b * coverNumber B Y ≤ a * coverNumber M X + payment s e j - (foundation s e j/2)*coverNumber M X := by
  let L := (l.count.val:ℝ); let x := coverNumber M X; let y:= coverNumber B Y
  have hl : 0 < L  := by dsimp only [L]; exact_mod_cast l.count.property
  let a₀ := foundation s e j
  have hA : 0<a₀ := foundation_pos s e j
  have hc : l.count.val*y ≤ (l.count.val+10*x)*e.foot :=
    le_trans (Nat.mul_le_mul_left _ (Corona.cover_mono ht _)) (Corona.collapse l X M B hg hh e.radius)
  have hf : L*(y:ℝ) ≤ (L+10*(x:ℝ))*e.foot  := by dsimp only [L]; exact_mod_cast hc
  have hy : (y:ℝ) ≤ e.foot+10*(e.foot:ℝ)/L*x := by
    apply (le_of_mul_le_mul_left ?_ hl)
    refine hf.trans (le_of_eq ?_)
    field_simp
  have HP := mul_nonneg hA.le (show 0 ≤ (x:ℝ) by positivity)
  calc
    b * coverNumber B Y ≤ (s.o.A j+e.extra)*(e.foot+10*(e.foot:ℝ)/L*x) :=
      mul_le_mul he hy (by positivity) (hb.trans he)
    _ = payment s e j + (10*e.foot*(s.o.A j+e.extra)/L)*x := by unfold payment; ring
    _ ≤ payment s e j + a₀/4*x :=
      add_le_add_right (mul_le_mul_of_nonneg_right h.exchange (by positivity)) _
    _ ≤ payment s e j+a*(x:ℝ)-a₀/2*x := by
      have hK := mul_le_mul_of_nonneg_right ha (show 0 ≤ (x:ℝ) by positivity)
      change a₀*_≤_ at hK
      linarith
    _ = _ := by ring

/-- One possible halo add-on includes old support AND the one-time flag
layer (even computations returning zero can need to read that). This is real
testing by `inspected`. -/
lemma flag_layer (X : Support f) : inspected X ⊆ halo 8 X := by
  have hv (x y : Site f) (W : Walk) (h : y ∈ visits x W) : separation x y ≤ W.length := by
    induction W generalizing x with
    | nil => simp only [Lattice.visits,List.mem_singleton] at h; rw [h]; simp
    | cons a r ih =>
      rcases List.mem_cons.mp h with e|e
      · rw [e]; simp
      have hh := ih _ e
      have ha : separation x (x+a.vec) ≤ 1 := by
        rw [separation_comm, separation, add_comm,add_sub_cancel_right,Step.vec]; split
        · rw [pdist_neg]; exact pdist_step _
        exact pdist_step _
      refine le_trans (separation_triangle _ (x+a.vec) _) ?_
      rw [List.length_cons]
      omega
  intro y hy; unfold inspected at hy
  rcases mem_union.mp hy with h|h
  · exact halo_subset _ _ h
  obtain ⟨p,-,hp⟩ := mem_biUnion.mp h
  split_ifs at hp with he
  · simp at hp
  obtain ⟨x,hx,hx'⟩:=not_disjoint_iff.mp he
  refine halo_spec.mpr ⟨x,hx,le_trans (separation_triangle x p.1 y) ?_⟩
  rw [separation_comm x p.1]
  exact add_le_add (hv _ _ (square _ _) (List.mem_toFinset.mp hx')) (hv _ _ (square _ _) (List.mem_toFinset.mp hp))

lemma projects_inspected (l : Ratio c f) (B : ℕ) (hB : 9 ≤ B) (r : ℕ) (X : Support f) :
    halo (r*B) ((inspected X).image l.parent) ⊆ halo ((r+1)*B) (X.image l.parent) := by
  intro y hy
  obtain ⟨u,hu,hj⟩:=halo_spec.mp hy
  obtain ⟨a,ha,rfl⟩:=mem_image.mp hu
  obtain ⟨x,hx,hv⟩:=halo_spec.mp (flag_layer X ha)
  have hl : 1 ≤ l.count.val := l.count.property
  have he : separation (l.parent x) (l.parent a) ≤ B := by
    have hh := Corona.foreshorten l x a
    apply Nat.le_of_mul_le_mul_left _ hl
    nlinarith only [hv,hB,hl,hh]
  exact halo_spec.mpr ⟨_,mem_image_of_mem _ hx,le_trans (separation_triangle _ (l.parent a) _) (by rw [Nat.add_mul];omega)⟩

private lemma embed_dist (l : Ratio c f) (x y : Site c) :
    separation (l.embed x) (l.embed y) ≤ l.count.val * separation x y := by
  unfold separation; rw [← l.root_embed,← l.root_embed,← map_sub,l.root_embed]
  refine Finset.sup_le ?_; intro i hi
  rw [l.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (component_le _ _)

/-- Group fine anchors by old cover number t. Radius of ball needed in fine
NATIVE units. -/
private def measureBall (L B r t : ℕ) := B * L * (r+20) * (t+1)

private lemma fine_hit (l : Ratio c f) (x : Support f) (o : Site f) (ho : o∈x) {Y : Support c} {y}
    {r M B : ℕ} (hg : 0 < B) (hm : M ≤ 2*B) (ht : Footage l r B x Y) (hy : y∈Y) :
    separation (l.embed y) o ≤ measureBall l.count.val B r (coverNumber M x) := by
  let L := l.count.val; have hl : 1 ≤ L := l.count.property
  obtain ⟨j,hj,hJ⟩:=halo_spec.mp (ht hy)
  obtain ⟨a,ha,rfl⟩:=mem_image.mp hj
  have hv := Corona.extent x M ha ho
  have he := le_trans (embed_dist l y (l.parent a)) (Nat.mul_le_mul_left L (show separation y _ ≤ r*B from separation_comm _ y ▸ hJ))
  have hh := Corona.near l a; rw [separation_comm a _] at hh
  have hx := separation_triangle (l.embed y) (l.embed (l.parent a)) a
  have H := separation_triangle (l.embed y) a o
  generalize hn : coverNumber M x=n at *
  -- collect terms B*L*r+L+ n*(8B+2)+4B
  have hn : separation (l.embed y) o ≤ B*L*r+L+(n*(8*B+2)+4*B) := by
    change 2*_≤L at hh
    rw [show B*L*r=L*(r*B) by ring]
    have hk : n*(4*M+2) ≤ n*(8*B+2) := Nat.mul_le_mul_left _ (by omega)
    omega
  unfold measureBall; refine hn.trans ?_
  -- n*(8*B+2) ≤ n*10*B*L
  change _ ≤ B*L*(r+20)*(n+1)
  have hB : B ≤ B*L := Nat.le_mul_of_pos_right _ hl
  have hL : L ≤ B*L := Nat.le_mul_of_pos_left _ hg
  have hn' : n*(8*B+2) ≤ n*(10*(B*L)) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; nlinarith only [hB,hL,hn',Nat.zero_le (B*L*r*n)]

/-- Convergence of the cover-count charge with any fixed power. -/
def decay (p : ℕ) (r : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)^p * Real.exp (-r*n)

lemma decay_summable (p : ℕ) (r : ℝ) (hr : 0 < r) : Summable (decay p r) := by
  have hi := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
  refine (hi.mul_right (Real.exp r)).congr ?_
  intro b; unfold decay
  push_cast; rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- Absolute per-output-hit cost INCLUDING an extra `foundation/4`
fine-cover exponential reserve per address and ANY power (fixed pre-L, or,
when an operation can use a post-L constant, chosen post-L). -/
def footprintCost (s : Survey G) (j : ℕ) (e : Exchange) (p L B : ℕ) :=
    let base := 3*B*L*(e.radius+20)
    Real.exp (payment s e j) * (base:ℝ)^ (4:ℕ) * ∑' t, decay (p+4) (foundation s e j/4) t

lemma footprintCost_pos (s : Survey G) (j) (e) (p L B) (hL : 0 < L) (hB : 0 < B) :
    0 < footprintCost s j e p L B := by
  let r := foundation s e j/4
  have hh := decay_summable (p+4) r (show 0 < r from div_pos (foundation_pos s e j) (by norm_num))
  have h := hh.sum_le_tsum ({0}:Finset ℕ) (fun x _ => show 0 ≤ decay (p+4) r x by unfold decay; positivity)
  have H : 0 < ∑' t, decay (p+4) (foundation s e j/4) t := by
    simpa only using (lt_of_lt_of_le (by simp [decay]) h)
  unfold footprintCost
  dsimp only
  positivity

private lemma partitionTest {ι : Type*} {F : ι → ℝ} {d : ι → ℕ} (t : Finset ι) :
    ∑ i ∈ t, F i = ∑ j ∈ t.image d, ∑ i ∈ t, if d i=j then F i else 0 := by
  classical
  rw [sum_comm]; apply sum_congr rfl; intro i hi
  simp [mem_image_of_mem d hi]

set_option maxHeartbeats 800000 in
lemma Buy.hit {ι : Type*} (l : Ratio c f) (h : Buy s q e j i l.count.val) (a b : ℝ)
    (ha : foundation s e j ≤ a) (hb : 0 ≤ b) (he : b ≤ s.o.A j+e.extra) {M B : ℕ}
    (hg : 0 < B) (hh : M ≤ 2*B) (X : ι → Support f) (o : ι → Site f) (ho : ∀ i,o i ∈ X i)
    (Y : ι → Support c) (ht : ∀ i,Footage l e.radius B (X i) (Y i)) (k : ℕ)
    (F : ι → ℝ) (hn : ∀ i,0 ≤ F i) (δ : ℝ) (hd : 0 ≤ δ)
    (hf : ∀ x : Site f, SumBudget (fun i => if o i=x then Real.exp (a*coverNumber M (X i))*F i else 0) δ) :
    ∀ y : Site c, SumBudget (fun i => if y ∈ Y i then
      Real.exp (b*coverNumber B (Y i)+(foundation s e j/4)*coverNumber M (X i))*((coverNumber M (X i):ℝ)+1)^k*F i else 0)
      (footprintCost s j e k l.count.val B * δ) := by
  classical
  intro y
  let d i := coverNumber M (X i)
  let A := payment s e j
  let r := foundation s e j/4
  let C := 3*B*l.count.val*(e.radius+20)
  let fns (x : Site f) i := if o i=x then Real.exp (a*d i)*F i else 0
  let t (i : ι) := if y∈Y i then Real.exp (b*coverNumber B (Y i)+r*d i)*((d i:ℝ)+1)^k*F i else 0
  let Q (x : ℕ) := halo (measureBall l.count.val B e.radius x) {l.embed y}
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i; unfold t; split
    · have := hn i; positivity
    exact le_rfl
  have hr0 : 0 < r := div_pos (foundation_pos ..) (by norm_num)
  have H : ∀ w : Finset ι, ∑ i∈w,t i ≤ footprintCost s j e k l.count.val B*δ := by
    intro w
    have hp (x : ℕ) : ∑ i∈w,(if d i=x then t i else 0) ≤ Real.exp A*decay (k+4) r x*C^ (4:ℕ)*δ := by
      have hv (i : ι) : (if d i=x then t i else 0) ≤
          Real.exp A * decay k r x * ∑ z∈ Q x, fns z i := by
        have he0 : 0 ≤ ∑ z∈ Q x, fns z i := Finset.sum_nonneg fun z _ => (hf z).1 i
        have ho0 : 0 ≤ decay k r x := by unfold decay; positivity
        by_cases hx : d i=x
        · rw [if_pos hx]
          unfold t
          by_cases hy : y∈Y i
          · rw [if_pos hy,hx]
            have he1 : o i ∈ Q x := halo_spec.mpr ⟨_,mem_singleton.mpr rfl,hx ▸ fine_hit l (X i) (o i) (ho i) hg hh (ht i) hy⟩
            calc
              _ ≤ Real.exp (a*x+A-r*x)*((x:ℝ)+1)^k*F i := by
                have hz:= h.footage l a b ha hb he hg hh (X i) (Y i) (ht i)
                change _ ≤ a*(d i)+A-_*(d i) at hz
                rw [hx] at hz
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (by positivity)) (hn i)
                unfold r; linarith
              _ = Real.exp A*decay k r x*fns (o i) i := by
                unfold fns decay; rw [if_pos rfl,hx, sub_eq_add_neg, Real.exp_add, Real.exp_add,neg_mul]; ring
              _ ≤ _ := mul_le_mul_of_nonneg_left (single_le_sum (fun z _ => (hf z).1 i) he1) (by positivity)
          rw [if_neg hy]
          positivity
        rw [if_neg hx]; positivity
      have hc (z : Site f) : ∑ i ∈ w, fns z i ≤ δ :=
        ((hf z).2.1.sum_le_tsum w (fun i _ ↦ (hf z).1 i)).trans (hf z).2.2
      have hL : 0<l.count.val:=l.count.property
      have hq : (Q x).card ≤ C^4*(x+1)^4 := by
        unfold Q
        refine le_trans (Corona.halo_size {l.embed y} _) ?_
        rw [card_singleton,one_mul, ← mul_pow]; apply Nat.pow_le_pow_left
        unfold C
        have hi : 0 < measureBall l.count.val B e.radius x := by unfold measureBall; positivity
        rw [show 3*B*l.count.val*(e.radius+20)*(x+1)=3*measureBall l.count.val B e.radius x by unfold measureBall; ring]; omega
      calc
        _ ≤ ∑ i ∈ w, Real.exp A * decay k r x * ∑ z∈ Q x, fns z i := Finset.sum_le_sum fun i _ => hv i
        _ = Real.exp A*decay k r x*∑ z∈Q x, ∑ i∈w, fns z i := by rw [← mul_sum,sum_comm]
        _ ≤ Real.exp A*decay k r x*∑ _z∈ Q x, δ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hc i) (by unfold decay; positivity)
        _ ≤ Real.exp A*decay k r x * ((C^ (4:ℕ):ℝ)*((x:ℝ)+1)^ (4:ℕ)*δ) := by
          rw [Finset.sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_left _ (by unfold decay; positivity)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hd
        _ = _ := by unfold decay; rw [pow_add]; ring
    rw [partitionTest (d:=d) w]
    apply le_trans (Finset.sum_le_sum (fun i _ => hp i))
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    have hS := (decay_summable (k+4) r hr0).sum_le_tsum (Finset.image d w) (fun i _ => by unfold decay; positivity)
    unfold footprintCost
    dsimp only
    -- normalize mul order
    calc
      _ ≤ Real.exp A*(∑' i, decay (k+4) r i)*(C:ℝ)^ (4:ℕ)*δ := by gcongr
      _ = _ := by change _ = Real.exp A * (C:ℝ)^ (4:ℕ) * _ * _; ring
  exact ⟨ht0, summable_of_sum_le ht0 H,Real.tsum_le_of_sum_le ht0 H⟩
/-- If testing only at the projected old *anchor*, pay exactly the sites
per residue cell instead of costs growing with B. E.g. the `L⁻⁵` part in
 needs this. -/
def localCost (s : Survey G) (j : ℕ) (e : Exchange) (p : ℕ) :=
    Real.exp (payment s e j) * ∑' t, decay p (foundation s e j/4) t

lemma Buy.aligned {ι : Type*} (l : Ratio c f) (h : Buy s q e j i l.count.val) (a b : ℝ)
    (ha : foundation s e j ≤ a) (hb : 0 ≤ b) (he : b ≤ s.o.A j+e.extra) {M B : ℕ}
    (hg : 0 < B) (hh : M ≤ 2*B) (X : ι → Support f) (o : ι → Site f)
    (Y : ι → Support c) (ht : ∀ i,Footage l e.radius B (X i) (Y i)) (k : ℕ)
    (F : ι → ℝ) (hn : ∀ i,0 ≤ F i) (δ : ℝ)
    (hf : ∀ x : Site f, SumBudget (fun i => if o i=x then Real.exp (a*coverNumber M (X i))*F i else 0) δ) :
    ∀ y : Site c, SumBudget (fun i => if l.parent (o i)=y then
      Real.exp (b*coverNumber B (Y i)+(foundation s e j/4)*coverNumber M (X i))*((coverNumber M (X i):ℝ)+1)^k*F i else 0)
      (localCost s j e k * ((l.count.val:ℝ)^ (4:ℕ) * δ)) := by
  classical
  intro y
  let d i := coverNumber M (X i)
  let fns (x : Site f) i := if o i=x then Real.exp (a*d i)*F i else 0
  let C := localCost s j e k
  let A := payment s e j
  let r := foundation s e j/4
  let p i := if l.parent (o i)=y then Real.exp (b*coverNumber B (Y i)+r*d i)*((d i:ℝ)+1)^k*F i else 0
  have hd (n) : 0 ≤ decay k r n := by unfold decay; positivity
  have hC : 0 ≤ C := mul_nonneg (Real.exp_nonneg _) (tsum_nonneg hd)
  have hp (i) : 0 ≤ p i := by have := hn i; dsimp only [p]; split_ifs <;> positivity
  let P (z : Site l.count) := l.splitSites.symm (y,z)
  have hz (i) : p i ≤ C*∑ z : Site l.count, fns (P z) i := by
    unfold p; split_ifs with hO
    · let n := l.residue (o i)
      have hzz : P n=o i := by unfold P; apply l.splitSites.injective; rw [l.splitSites.apply_symm_apply,← l.unpack,hO]
      apply le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun z => fns (P z) i)
        (fun m _ => (hf _).1 i) (mem_univ n)) hC)
      rw [hzz]
      have hv := h.footage l a b ha hb he hg hh (X i) (Y i) (ht i)
      have hw := decay_summable k r (show 0<r from div_pos (foundation_pos ..) (by norm_num))
      have hb0 : decay k r (d i) ≤ ∑' t, decay k r t := by
        simpa using hw.sum_le_tsum ({d i}:Finset ℕ) (fun n _ => hd n)
      calc
        _ ≤ Real.exp (a*d i+A-r*d i)*((d i:ℝ)+1)^k*F i := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (by positivity)) (hn i)
          dsimp only [d,A,r]; linarith
        _ = (Real.exp A * decay k r (d i))*fns (o i) i := by
          unfold fns decay; rw [if_pos rfl, sub_eq_add_neg,Real.exp_add,Real.exp_add,neg_mul]; ring
        _ ≤ C*fns (o i) i := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb0 (Real.exp_nonneg _)) ((hf _).1 _)
    exact mul_nonneg hC (sum_nonneg fun z _ => (hf _).1 i)
  have hH (w : Finset ι) : ∑ i∈w,p i ≤ C*((l.count.val:ℝ)^ (4:ℕ)*δ) := by
    apply le_trans (Finset.sum_le_sum (fun i _ => hz i))
    rw [← mul_sum,sum_comm]; apply mul_le_mul_of_nonneg_left _ hC
    have hQ (z : Site l.count) : ∑ i∈w,fns (P z) i ≤ δ :=
      ((hf _).2.1.sum_le_tsum w (fun i _ => (hf _).1 i)).trans (hf _).2.2
    apply le_trans (Finset.sum_le_sum (fun z _ => hQ z)); rw [sum_const,card_univ,Lattice.site_card]
    rw [nsmul_eq_mul]; push_cast; rfl
  exact ⟨hp,summable_of_sum_le hp hH, Real.tsum_le_of_sum_le hp hH⟩

/-- The two types of actual input. Keep the same derivative and support
certificate.
Don't change `Healthy` when masks on the threshold. -/
def reuseCharge {c f : Side} (s : Survey G) (j : ℕ) (e : Exchange) (X : ℕ → Support f) (Y : ℕ → Support c)
    (M B k : ℕ) (b : ℝ) (F : ℕ → ℝ) (δ : ℝ) : Prop := ∀ y : Site c,
    SumBudget (fun i => if y∈Y i then Real.exp (b*coverNumber B (Y i)+(foundation s e j/4)*coverNumber M (X i))*
      ((coverNumber M (X i):ℝ)+1)^k*F i else 0) δ

lemma Buy.fromE (l : Ratio c f) (h : Buy s q e j i l.count.val) {T : Activities G f} {δ : ℝ} {p : BudgetPoint}
    (hT : T.EBound p δ) (b : ℝ)
    (ha : foundation s e j ≤ p.supportExponent) (hb : 0 ≤ b) (he : b ≤ s.o.A j+e.extra) {B : ℕ}
    (hg : 0<B) (hh : p.B ≤ 2*B) (hd : 0 ≤ δ) : ∃ F : ℕ → ℝ,
      (∀ i,p.supBounds (T.reg i).site (T.reg i).support (T.E i) (F i)) ∧
      ∀ Y, (∀ i,Footage l e.radius B (T.reg i).support (Y i)) → ∀ k,
        reuseCharge s j e (fun i => (T.reg i).support) Y p.B B k b F (footprintCost s j e k l.count.val B * δ) := by
  obtain ⟨F,hF,Hf⟩ := hT
  exact ⟨F,hF,fun Y hY k => h.hit l _ b ha hb he hg hh _ _ (fun i => (T.reg i).anchor) Y hY k F
    (fun i => (hF i).1) δ hd Hf⟩

lemma Buy.fromK (l : Ratio c f) (h : Buy s q e j i l.count.val) {T : Activities G f} {δ : ℝ} {p : BudgetPoint}
    (hT : T.KBound p δ) (b : ℝ)
    (ha : foundation s e j ≤ p.supportExponent) (hb : 0 ≤ b) (he : b ≤ s.o.A j+e.extra) {B : ℕ}
    (hg : 0<B) (hh : p.B ≤ 2*B) (hd : 0 ≤ δ) : ∃ F : ℕ → ℝ,
      (∀ i,(0 ≤ F i) ∧ ∀ U, ‖T.K i U‖ ≤ F i) ∧
      ∀ Y, (∀ i,Footage l e.radius B (T.forced i).support (Y i)) → ∀ k,
        reuseCharge s j e (fun i => (T.forced i).support) Y p.B B k b F (footprintCost s j e k l.count.val B * δ) := by
  obtain ⟨F,hF,Hf⟩ := hT
  choose o ho using fun i => ((T.forced i).inventory_ne.mono (T.forced i).inventory_sup)
  refine ⟨F,hF,fun Y hY k => h.hit l _ b ha hb he hg hh _ o ho Y hY k F
    (fun i => (hF i).1) δ hd ?_⟩
  intro x
  have he := Hf x
  let t n := if o n=x then p.mass (T.forced n).support (F n) else 0
  have hp (i : ℕ) : 0 ≤ t i := by
    have := (hF i).1; unfold t BudgetPoint.mass; split_ifs <;> positivity
  have ht (i) : t i ≤ (if x ∈ (T.forced i).support then p.mass (T.forced i).support (F i) else 0) := by
    unfold t; split_ifs with h hx hx
    · exact le_rfl
    · exact False.elim (hx (h ▸ ho i))
    · have := (hF i).1; unfold BudgetPoint.mass; positivity
    exact le_rfl
  have h := he.2.1.of_nonneg_of_le hp ht
  exact ⟨hp,h,(h.tsum_le_tsum ht he.2.1).trans he.2.2⟩
end YM.Next.Scheduling
