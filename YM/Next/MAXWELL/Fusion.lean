import YM.Maxwell.Reorder

/-!
# Removing one leg

Unpack equation directly on Wick's occurrence matching convention; this
avoids normal-order combinatorial factors being implicit when
translating the free tables. The recurrence below is only used with
positions in `Conf`. Works including n=1, repeated components,
zero-degree spectators.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Wick
open Function Set Filter Finset Occ
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {n : ℕ} {W U : Powers G n}

def grow (W : Powers G n) (i : Fin n) (s : Slot G) := update W i (W i + Finsupp.single s 1)

def less (W : Powers G n) (p : Occ W) : Powers G n :=
    update W p.label (W p.label - Finsupp.single p.probe 1)

lemma undo (p : Occ W) : grow (less W p) p.label p.probe = W := by
  funext i
  by_cases h : i=p.label
  · subst i; unfold less grow; simp only [update_self]; apply tsub_add_cancel_of_le
    intro s; by_cases he : p.probe=s
    · subst s; simp only [Finsupp.single_eq_same]
      have ht := p.legit; omega
    simp [he]
  simp [grow,less, update_of_ne h]

/-- One added letter. -/
lemma option_leg (W : Powers G n) (i : Fin n) (s : Slot G) :
    ∃ e : Option (Occ W) ≃ Occ (grow W i s),
      (e none).label=i ∧ (e none).probe=s ∧
      (∀ p : Occ W, (e (some p)).label=p.label) ∧ ∀ p : Occ W, (e (some p)).probe=p.probe := by
  classical
  let L := grow W i s
  have he (a : Fin n) (b : Slot G) : L a b = (if a=i ∧ b=s then W a b+1 else W a b) := by
    by_cases h : a=i
    · subst a; by_cases h : b=s <;> simp_all [L,grow,eq_comm]
    simp [L,grow,h]
  let f : Option (Occ W) → Occ L
    | none => atSlot i s (W i s) (by simp [he])
    | some p => atSlot p.label p.probe p.index (by rw [he]; have h := p.legit; split_ifs <;> omega)
  have hh (p : Occ W) : f none ≠ f (some p) := by
    intro hw
    have ha : i=p.label := congr_arg (label (W:=L)) hw
    have hb : s=p.probe := congr_arg (Occ.probe (W:=L)) hw
    have ht : W i s=p.index := congr_arg (index (W:=L)) hw
    have hp := p.legit; rw [ha,hb] at ht; omega
  have hi : Injective f := by
    rintro (_ | p) (_ | q) H
    · rfl
    · exact (hh q H).elim
    · exact (hh p H.symm).elim
    exact congr_arg some (Occ.ext (congr_arg (label (W:=L)) H) (congr_arg (Occ.probe (W:=L)) H) (congr_arg (index (W:=L)) H))
  have hs : Surjective f := by
    intro q
    by_cases h : q.index < W q.label q.probe
    · exact ⟨some (atSlot q.label q.probe q.index h),Occ.ext rfl rfl rfl⟩
    have ht := q.legit; rw [he] at ht
    split_ifs at ht with H
    · refine ⟨none, Occ.ext H.1.symm H.2.symm ?_⟩
      change W i s=q.index; rw [← H.1,← H.2]; omega
    exact (h ht).elim
  exact ⟨Equiv.ofBijective f ⟨hi,hs⟩,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

lemma less_leg (W : Powers G n) (p : Occ W) :
    ∃ e : Option (Occ (less W p)) ≃ Occ W, e none=p ∧
      (∀ p, (e (some p)).label=p.label) ∧ ∀ p : Occ (less W p), (e (some p)).probe=p.probe := by
  classical
  have he := option_leg (less W p) p.label p.probe
  rw [undo] at he
  obtain ⟨e,ha,hb,hf,hg⟩ := he
  let S := Equiv.swap (e none) p
  refine ⟨e.trans S,Equiv.swap_apply_left _ _, fun q => ?_, fun q => ?_⟩
  all_goals
    simp only [Equiv.trans_apply,S,Equiv.swap_apply_def]; split_ifs with h h'
    · simp at h
  · exact ha.trans ((congr_arg label h').symm.trans (hf q))
  · exact hf q
  · exact hb.trans ((congr_arg Occ.probe h').symm.trans (hg q))
  exact hg q

/-- Remove one pair from an abstract occurrence bijection, paying the exact
edge weight. The deleted legs stand at `none`, `some none`. -/
private theorem fuse_pair (x : Points n) (H : x ∈ conf n)
    (e : Option (Option (Occ U)) ≃ Occ W) (hh : (e none).label≠(e (some none)).label)
    (hl : ∀ p : Occ U, (e (some (some p))).label = p.label)
    (hp : ∀ p : Occ U, (e (some (some p))).probe = p.probe) :
    (∑ v ∈ (Finset.univ.filter (fun v : Matching W => partner v (e none)=e (some none))), graph x v) =
      edge x (e none) (e (some none)) * Wick.monomial x U := by
  classical
  let A := e none
  let B := e (some none)
  let f (p : Occ U) := e (some (some p))
  have hi : Injective f := fun i j h => Option.some.inj (Option.some.inj (e.injective h))
  have he (p : Occ W) : p=A ∨ p=B ∨ ∃ q, p=f q := by
    obtain ⟨(_|(_|q)),rfl⟩ := e.surjective p
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    exact Or.inr (Or.inr ⟨q,rfl⟩)
  have hA (p) : f p ≠ A := by simp [f,A]
  have hB (p) : f p ≠ B := by simp [f,B]
  -- For each reduced matching, construct a full one.
  have pair (P : Matching U) : ∃ Q : Matching W, partner Q A=B ∧ ∀ p : Occ U, partner Q (f p)= f (partner P p) := by
    let g : Option (Option (Occ U)) → Option (Option (Occ U))
      | none => some none
      | some none => none
      | some (some q) => some (some (partner P q))
    have hg : Involutive g := by rintro (_|(_|q)) <;> simp [g]
    let t : Equiv.Perm (Occ W) := (e.symm.trans (hg.toPerm g)).trans e
    have ht (x) : t (e x)=e (g x) := by simp [t]
    have Ht : t*t=1 := by
      ext1 w; obtain ⟨v,rfl⟩ := e.surjective w
      change t (t (e v))=e v; rw [ht, ht,hg v]
    have Hs (v : Occ W) : (t v).label ≠ v.label := by
      obtain ⟨(_|(_|q)),rfl⟩ := e.surjective v
      · rw [ht]; exact hh.symm
      · rw [ht]; exact hh
      rw [ht]; change (e (some (some (partner P q)))).label ≠ _
      rw [hl,hl]; exact different P q
    exact ⟨⟨t,Ht,Hs⟩,ht none,fun p => ht _⟩
  choose V hv hs using pair
  let F : Finset (Matching W) := Finset.univ.filter fun v : Matching W => partner v A=B
  rw [monomial,mul_sum]; symm
  change (∑ v : Matching U, _) = ∑ w ∈ F, _
  refine sum_bij (fun P _ => V P) (fun P _ => mem_filter.mpr ⟨mem_univ _,hv P⟩) ?_ ?_ (fun P _ => ?_)
  · intro a _ b _ ht
    apply Subtype.ext; apply Equiv.ext; intro q
    change partner a q = partner b q
    apply hi; rw [← hs,ht,hs]
  · intro w hw
    have hu : partner w A=B := (mem_filter.mp hw).2
    have ht : partner w B=A := hu ▸ turn w A
    have hx (p) : ∃ q, partner w (f p) = f q :=
      ((he _).resolve_left (fun H => hB p ((partner w).injective (H.trans ht.symm)))).resolve_left
        (fun H => hA p ((partner w).injective (H.trans hu.symm)))
    choose g hg using hx
    have hh : Involutive g := by intro p; apply hi; rw [← hg, ← hg, turn]
    let Q : Matching U := ⟨hh.toPerm g, Equiv.ext fun p => hh p, fun v => by
      change (g v).label ≠ v.label
      have he := different w (f v); rw [hg] at he
      unfold f at he
      rw [hl,hl] at he; exact he⟩
    refine ⟨Q,mem_univ _,?_⟩
    apply Subtype.ext; apply Equiv.ext; intro y
    change partner (V Q) y = partner w y
    rcases he y with rfl|rfl|⟨p,rfl⟩
    · rw [hv Q,hu]
    · rw [ht,← hv Q,turn]
    rw [hs]; exact (hg p).symm
  let c := toCorner (V P) A
  have hc : c = A ∧ partner (V P) c=B ∨ c=B ∧ partner (V P) c=A := by
    dsimp only [c]; unfold toCorner; split_ifs
    · exact Or.inl ⟨rfl,hv P⟩
    exact Or.inr ⟨hv P,turn (V P) A⟩
  have hC : c ∈ corners (V P) := inside ..
  have hn (p) : f p ≠ c := by
    rcases hc with h | h
    · rw [h.1]; exact hA p
    rw [h.1]; exact hB p
  have hy q : f q ∈ corners (V P) ↔ q ∈ corners P := by
    simp only [corners,mem_filter,Finset.mem_univ,true_and,hs,f,hl]
  have hw : graph x P = ∏ q ∈ (corners (V P)).erase c, edge x q (partner (V P) q) := by
    refine prod_bij (fun p _ => f p) (fun p hp => mem_erase.mpr ⟨hn p,(hy p).mpr hp⟩)
      (fun p _ q _ ht => hi ht) ?_ ?_
    · intro y hY
      obtain ⟨hne,hy'⟩ := mem_erase.mp hY
      rcases he y with H|H|⟨p,H⟩
      · exfalso
        subst y; exact hne (fixed _ hy').symm
      · exfalso
        subst y; apply hne
        calc
          B = toCorner (V P) B := (fixed _ hy').symm
          _ = c := by rw [← hv, canonical]
      subst y; exact ⟨p,(hy p).mp hy',rfl⟩
    intro p _; rw [hs]; simp [edge,f,hl,hp]
  change edge x A B * graph x P = ∏ p ∈ corners (V P), edge x p (partner (V P) p)
  rw [← mul_prod_erase _ _ hC, hw]; congr 1
  rcases hc with ⟨h,h'⟩|⟨h,h'⟩ <;> rw [h',h]
  exact entry_symmetric _ _ ((show Injective x.ofLp from H).ne hh)

lemma mon_growth (x : Points n) (H : x ∈ conf n) (W : Powers G n) (i : Fin n) (s : Slot G) :
    Wick.monomial x (grow W i s) = ∑ q : Occ W, if q.label=i then 0 else
      entry s q.probe (x i) (x q.label) * Wick.monomial x (less W q) := by
  classical
  let U := grow W i s
  obtain ⟨e,ha,hb,hc,hd⟩ := option_leg W i s
  let F (q : Occ W) := (Finset.univ.filter fun v : Matching U => partner v (e none)=e (some q))
  calc
    _ = ∑ q : Occ W, ∑ v ∈ F q, graph x v := by
      unfold Wick.monomial; symm
      simp_rw [F,sum_filter]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _
      obtain ⟨a,h⟩ := e.surjective (partner v (e none))
      rcases a with _|a
      · exact ((different v (e none)) (congr_arg (label (W:=U)) h.symm)).elim
      rw [← h]; simp
    _ = _ := by
      apply Finset.sum_congr rfl; intro q _
      split_ifs with h
      · exact Finset.sum_eq_zero fun v hv => ((different v (e none)) (by rw [(mem_filter.mp hv).2,hc,ha,h])).elim
      obtain ⟨k,hk,hf,hp⟩ := less_leg W q
      let L := (Equiv.optionCongr k).trans e
      have hv : L none=e none := rfl
      have he : L (some none) = e (some q) := by simp [L,hk]
      have hw (p : Occ (less W q)) : L (some (some p)) = e (some (k (some p))) := rfl
      have hh : (L none).label≠(L (some none)).label := by rw [hv,he,hc,ha]; exact Ne.symm h
      have ht := fuse_pair x H L hh (fun p => by rw [hw,hc,hf]) (fun p => by rw [hw,hd,hp])
      rw [hv,he] at ht
      simp only [edge,hc,hd,ha,hb] at ht
      exact ht

end YM.Maxwell.Wick
