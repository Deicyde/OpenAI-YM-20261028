import YM.Next.RANK.EntryWord


/-!
# Support pricing at restart (large radius on same lattice)

Here d is the price on the true torus including narrow directions and
all actual walks. Expenses recovered when the radius test is tightened. No
claim that an operator needs exactly these reads is made by the pricing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Thirst
open Function Lattice Wilson RG Finset Relation Corona
open scoped Classical BigOperators

variable {n : Side}

-- enlarge radius at unchanged scale. Use old connected support and flag probes.
lemma widen (p q u : ℕ) (hp : 0<p) (hh : p≤q) (hu : u ≤ q) (X : Support n) :
    q*coverNumber q (halo u X) ≤ 100000*(q + p * coverNumber p X) := by
  obtain ⟨F,H,h₁⟩ := coverNumber_realized p X
  obtain ⟨k,hk,A,h₂,h₃⟩ := Corona.ring_path _ (Corona.halo_ship p H.2)
  have hq := hp.trans_le hh
  let D := (Finset.range (k/q+1)).image (fun i=> A (i*q))
  have hz (i) (H : i<k/q+1) : i*q ≤ k := (Nat.le_div_iff_mul_le hq).mp (by omega)
  have ht : q * D.card ≤ k + q := by
    have h : D.card≤ k/q+1 := Finset.card_image_le.trans (by rw [card_range])
    apply (Nat.mul_le_mul_left q h).trans
    rw [Nat.mul_succ,mul_comm q]; exact Nat.add_le_add_right (hz _ (by omega)) _
  have ha : Ships D ((3*q)+(3*q)+1) := by
    intro i hi j hj
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hi
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    have hi (i) (h : i∈range (k/q+1)) : ReflTransGen (Touch D (3*q+(3*q)+1)) (A (0*q)) (A (i*q)) := by
      rw [mem_range] at h
      apply line_path (F:=fun j=>A (j*q))
      · exact fun j H => mem_image_of_mem _ (mem_range.mpr (H.trans_lt h))
      intro j H; have hT:=path_span h₂ (j*q) ((j+1)*q) (by rw [Nat.succ_mul];omega) (hz _ (by omega)); rw [Nat.succ_mul] at hT ⊢; omega
    exact (Corona.sym (hi c hc)).trans (hi d hd)
  have he : covers (3*q) (halo u X) D := by
    refine ⟨?_, ship_halo _ ha⟩
    rintro x hx; obtain ⟨y,hy,hF⟩ := halo_spec.mp hx
    obtain ⟨e,he,hp'⟩ := halo_spec.mp (H.1 hy)
    obtain ⟨b,hb,hE⟩ := h₃ _ he
    refine halo_spec.mpr ⟨_, mem_image_of_mem (fun i=> A (i*q)) (mem_range.mpr (show b/q<k/q+1 from Nat.lt_add_one_iff.mpr (Nat.div_le_div_right hb))),?_⟩
    have h : separation (A (b/q*q)) e≤q:= by
      rw [← hE]; have hi:= Nat.div_add_mod b q; have hx:= Nat.mod_lt b hq
      have H : q*(b/q)=b/q*q := mul_comm ..
      exact (path_span h₂ _ _ (by omega) hb).trans (by omega)
    have hE := separation_triangle (A (b/q*q)) e y; have hf:= separation_triangle (A (b/q*q)) y x; omega
  apply (Nat.mul_le_mul_left q (tiling hq he)).trans
  rw [← mul_assoc];apply (Nat.mul_le_mul_right _ ht).trans
  rw [h₁] at hk; nlinarith only [hk, hq, hp]

lemma encumber (p q : ℕ) (h : p≤q) (X : Support n) : coverNumber q X ≤ coverNumber p X := by
  obtain ⟨F,⟨h1,h2⟩,h₁⟩ := coverNumber_realized p X
  apply le_trans _ h₁.le; apply list_cost; refine ⟨h1.trans (halo_mono h le_rfl),ship_halo _ ?_⟩
  have hx:= halo_ship p h2
  exact fun i hi j hj=>ReflTransGen.mono (fun a b (hp : Touch F (p+p+1) a b)=> ⟨hp.1,hp.2.1,hp.2.2.trans (by omega)⟩) _ _ (hx i hi j hj)

lemma inspect (X : Support n) : inspected X⊆ halo 8 X := by
  intro x h; rcases mem_union.mp h with he|he
  · exact halo_subset _ X he
  obtain ⟨p,hp,hv⟩ := mem_biUnion.mp he
  split at hv
  · simp at hv
  rename_i hg; obtain ⟨y,hy,hz⟩ := Finset.not_disjoint_iff.mp hg
  have h (z : Site n) (hz : z ∈ touched p) : separation p.1 z ≤ 4 := by
    have H (x y : Site n) (w : Walk) : x∈ visits y w → separation y x ≤ w.length := by
      induction w generalizing y with
      | nil => rintro h; simp only [visits,List.mem_singleton] at h; simp [h]
      | cons d w ih =>
        rintro h; rcases List.mem_cons.mp h with rfl|h
        · simp
        have hp : separation x (x + d.vec) ≤1:= by
          rw [separation_comm,separation,add_comm,add_sub_cancel_right,Step.vec]; split
          · rw [pdist_neg]; exact pdist_step ..
          exact pdist_step ..
        -- instantiate y, proof idem
        have hp' : separation y (y+d.vec) ≤1 := by simpa [separation] using hp
        exact (separation_triangle _ (y+d.vec) _).trans (by have H:=ih _ h; simp only [List.length_cons]; omega)
    exact H _ _ _ (List.mem_toFinset.mp hz)
  exact halo_spec.mpr ⟨_,hy,(separation_triangle _ p.1 _).trans (by rw [separation_comm y]; exact Nat.add_le_add (h y hz) (h x hv))⟩

-- walk support charge. use raw length every slot

def orbit (x : Site n) (w : Walk) := (visits x w).toFinset

lemma orbit_start (x : Site n) (w : Walk) : x∈orbit x w := by cases w <;> simp [orbit,visits]

lemma orbit_concat (x : Site n) (a b : Walk) : orbit x (a++b)=orbit x a∪orbit (stop x a) b := by
  induction a generalizing x with
  | nil => simp [orbit,visits,stop,insert_eq_of_mem (show x∈ (visits x b).toFinset from orbit_start x b)]
  | cons i a ih =>
    ext y; change y∈ (x :: visits (x+i.vec) (a++b)).toFinset ↔ y∈(x :: visits (x+i.vec) a).toFinset ∪ orbit (stop (x+i.vec) a) b
    simp only [List.toFinset_cons, mem_insert, mem_union]; change y=x ∨ y∈orbit (x+i.vec) (a++b) ↔ _; rw [ih,mem_union]; simp only [orbit];tauto

lemma orbit_bill (x : Site n) (w : Walk) : coverNumber 1 (orbit x w) ≤ w.length+1 := by
  induction w generalizing x with
  | nil =>
    have h : covers 1 (orbit x []) {x} := ⟨by simpa only [orbit,visits,List.toFinset_cons,List.toFinset_nil,insert_empty] using halo_subset 1 {x},ship_halo _ (by simp only [Ships, mem_singleton]; rintro a rfl i rfl; exact .refl)⟩
    exact (list_cost _ h).trans (by simp)
  | cons d w ih =>
    let y:= x+d.vec
    have H : separation x y ≤1 := by
      rw [separation_comm,separation,show y-x=d.vec by unfold y;abel,Step.vec]; split
      · rw [pdist_neg]; exact pdist_step ..
      exact pdist_step ..
    have h : covers 1 (orbit x [d]) {x} := ⟨by
      intro i hi; simp only [orbit,List.toFinset_cons,List.toFinset_nil,visits,Finset.insert_empty,mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl
      · simp [halo_spec]
      exact halo_spec.mpr ⟨x,by simp,H⟩,ship_halo _ (by simp only [Ships,mem_singleton]; rintro a rfl i rfl; exact .refl)⟩
    change coverNumber _ (orbit x ([d]++w))≤_
    rw [orbit_concat]
    apply (meets_sum (x:=y) (D:=orbit x [d]) (by simp [orbit,y,visits]) (show y∈orbit y w from orbit_start ..) _).trans
    apply (Nat.add_le_add (list_cost _ h) (ih (x+d.vec))).trans; rw [card_singleton,List.length_cons]; omega

def lives (x : Site n) (i : Slot) : Support n := i.stencil.image (fun a=>wrap n a+x)
lemma reached (x : Site n) (i : Slot) :
    lives x i= orbit x (i.walk ++ square i.plaq.val.1 i.plaq.val.2) := by
  have h (z : Cover) (w : Walk) : (visits z w).map (fun a => wrap n a+x)= visits (wrap n z+x) w := by
    induction w generalizing z with
    | nil => simp [visits]
    | cons a w ih => simp only [List.map_cons,visits,ih,map_add,wrap_vec,add_right_comm (wrap n z) x]
  have h' (z : Cover) (w : Walk) : stop (wrap n z+x) w= wrap n (stop z w)+x := by
    induction w generalizing z with
    | nil => simp [stop]
    | cons a w ih => simp only [stop,← ih, map_add,wrap_vec,add_right_comm (wrap n z) x]
  rw [orbit_concat]
  have hz : stop x i.walk=wrap n i.offset+x := by simpa only [map_zero,zero_add,Slot.offset] using! h' 0 i.walk
  have hf : orbit x i.walk= (visits (0:Cover) i.walk).toFinset.image (fun a=>wrap n a+x) := by
    have hl := h 0 i.walk; rw [map_zero,zero_add] at hl
    unfold orbit; rw [← hl]; ext; simp
  unfold lives Slot.stencil; rw [Finset.image_union,hz,hf]; congr 1; unfold orbit; rw [← h];ext; simp
lemma starts (x : Site n) (i : Slot) : x∈ lives x i := by rw [reached]; exact orbit_start ..
lemma qualifies (x : Site n) (i : Slot) : coverNumber 1 (lives x i) ≤ i.length+1 := by rw [reached]; exact (orbit_bill x _).trans (by rw [List.length_append]; exact le_rfl)

lemma stationed {G : Gauge} (x : Site n) (d : ℕ) (i : Atom G d) : x∈i.footprint x := by
  unfold Atom.footprint; simpa using! Finset.mem_image_of_mem (fun a=> wrap n a+x) (show 0∈ i.stencil from mem_insert_self ..)
lemma landed {G : Gauge} (x : Site n) (d : ℕ) (i : Atom G d) : coverNumber 1 (i.footprint x) ≤ i.length+d+1 := by
  have h₀ : coverNumber 1 ({x} : Support n) ≤ 1 := by simpa only [orbit,visits,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,List.length_nil,zero_add] using orbit_bill x []
  have ht (s : Finset (Fin d)) : coverNumber 1 ({x} ∪ s.biUnion (fun v=> lives x (i.leg v))) ≤ (∑ a∈s, (i.leg a).length)+ s.card +1 := by
    induction s using Finset.induction_on with
    | empty => simpa using h₀
    | insert a s ha ih =>
      rw [biUnion_insert,sum_insert ha,card_insert_of_notMem ha, Finset.union_left_comm]
      apply (meets_sum (starts x (i.leg a)) (X:={x}∪s.biUnion _) (by simp) 1).trans
      apply (Nat.add_le_add (qualifies x _) ih).trans; omega
  unfold Atom.length
  convert (ht Finset.univ) using 2
  · ext y; unfold Atom.footprint Atom.stencil; simp [lives]; grind
  simp
end YM.Next.Rank.Thirst
