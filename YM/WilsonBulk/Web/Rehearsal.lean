import YM.WilsonBulk.Web.Distance

/-!
# Large-period limits of printed supplies

To certify the *independent cover* Ward identities we'll compare period
diagrams by compounding transitions: `Proxy` of finite ordered kernels is a
cover presentation with a common positive width, representing the FINITE
objects including their winding images, tending to the cover quantities.
Strictness/pre-width for the RG recursion is not spent here; period limits
are algebraic aids at already fixed finite step data. These operations do not
justify any limit/analyticity claims about the full densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Filter Pert.Bulk Lattice Bloch Equiv

variable {α : Type} {D : ℕ→Side} {c : Side} {σ θ p q : ℝ} {n k m : ℕ}
variable {u v : Text α n}
abbrev Leaf (D : ℕ→Side) (α : Type) (n : ℕ) := ∀ i:ℕ,Page (Co (D i) α) n
def Proxy (V : Leaf D α n) (u : Text α n) :=
  ∃ σ p : ℝ, 0<σ ∧ ∃ F : ℕ→ Text α n, Tendsto F atTop (𝓝 u) ∧
    (∀ᶠ i in atTop,Pervasive (F i) ∧ Within (lawn α) σ p (F i) ∧ Orates (small (D i) α) (F i) (V i))
variable [Fintype α] (hd : Tendsto (fun i=> (D i).val) atTop atTop)
variable {V U : Leaf D α n}

omit [Fintype α] in
lemma sold (u : Text α (n+1)) (h : Pervasive u) (hu : Within (lawn α) σ p u) (hp : 0<σ) : Proxy (fun i=> print (D i) u) u :=
  ⟨σ,p,hp,fun _=>u,tendsto_const_nhds, Eventually.of_forall (fun _=> ⟨h,hu,reads h⟩)⟩
namespace Proxy

include hd
lemma uniq (h : Proxy V v) (hv : Proxy U u) (he : ∀ᶠ i in atTop, V i=U i) (hn : n ≠ 0) : v=u := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; obtain ⟨z,B,hz,g,H',q⟩:= hv
  ext1 y
  refine tendsto_nhds_unique_of_eventuallyEq (printed_limit hd (p.mono fun i hi=>hi.2.1) hx (p.mono fun i hi=>hi.2.2) H hn y) (printed_limit hd (q.mono fun i hi=>hi.2.1) hz (q.mono fun i hi=>hi.2.2) H' hn y) ?_
  exact he.mono (fun i hi=> congr_fun hi _)
omit hd
omit [Fintype α] in
lemma always (U : Leaf D α n) (u : Text α n) (h : ∀ᶠ i in atTop, Orates (small (D i) α) u (U i))
    (hu : Pervasive u) (he : Within (lawn α) σ p u) (hh : 0<σ) : Proxy U u :=
  ⟨σ,p,hh,fun _=>u,tendsto_const_nhds,h.mono (fun _ hi=>⟨hu,he,hi⟩)⟩
-- inherited convergence facts (we'll estimate directly later)
omit [Fintype α] in
lemma pervasive (h : Proxy U u) : Pervasive u := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; intro b y
  exact tendsto_nhds_unique_of_eventuallyEq (tendsto_pi_nhds.mp H (roll b α ∘ y)) (tendsto_pi_nhds.mp H y) (p.mono fun i hi=> hi.1 b y)
omit [Fintype α] in
lemma priced (h : Proxy U u) : ∃ σ p, 0<σ ∧ Within (lawn α) σ p u := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; refine ⟨x,A,hx,(within_budget ?_).mpr ?_⟩
  · obtain ⟨i,hi⟩:= p.exists; exact hi.2.1.1
  intro i a
  let c := fee (lawn α) x u i a
  have hc (s : Finset (Legs (Market α) n)) : ∑ b∈s,c b ≤ A := by
    let g (i' : ℕ) (b : Legs (Market α) n) := fee (lawn α) x (f i') i a b
    have ht b : Tendsto (fun j=> g j b) atTop (𝓝 (c b)) := by
      unfold c g fee; split
      · exact (tendsto_pi_nhds.mp H b).abs.mul_const _
      exact tendsto_const_nhds
    refine le_of_tendsto (tendsto_finsetSum s fun i _ => ht i) (p.mono fun j hj=>?_)
    have HH := (within_budget hj.2.1.1).1 hj.2.1 i a; exact (HH.2.1.sum_le_tsum _ (fun v _=> HH.1 _)).trans HH.2.2
  have hs : Summable c:= summable_of_sum_le (fee_nonneg · i a) hc
  exact ⟨(fee_nonneg · i a),hs,hs.tsum_le_of_sum_le hc⟩

omit [Fintype α] in
lemma zero : Proxy (0 : Leaf D α n) 0 := ⟨1,0,one_pos,fun _=>0,tendsto_const_nhds, Eventually.of_forall (fun _=>⟨Pervasive.zero, Within.zero le_rfl,Orates.zero⟩)⟩
omit [Fintype α] in
lemma eq (h : Proxy U u) (he : ∀ᶠ i:ℕ in atTop, U i= V i) : Proxy V u := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; exact ⟨x,A,hx,f,H,(p.and he).mono fun i ⟨g,e⟩=>e ▸ g⟩
omit [Fintype α] in
lemma plus (h : Proxy U u) (hv : Proxy V v) : Proxy (U+V) (u+v) := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; obtain ⟨z,B,hz,g,H',q⟩:= hv
  exact ⟨min x z,A+B,lt_min hx hz, f+g, H.add H', (p.and q).mono fun i ⟨⟨l,r,s⟩,⟨l',r',s'⟩⟩=>
    ⟨l.plus l', (r.mono (min_le_left ..) le_rfl).add (r'.mono (min_le_right ..) le_rfl), s.plus s' r r' hx.le hz.le⟩⟩
omit [Fintype α] in
lemma scale (h : Proxy U u) (r : ℝ) : Proxy (r • U) (r • u) := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; exact ⟨x,|r| * A,hx,r • f,H.const_smul _,p.mono fun i ⟨l,e,g⟩=>⟨l.scale r,e.scale r,g.scale r⟩⟩
omit [Fintype α] in
lemma minus (h : Proxy U u) (hv : Proxy V v) : Proxy (U-V) (u-v) := by simpa only [neg_smul,one_smul,sub_eq_add_neg] using h.plus (hv.scale (-1))
omit [Fintype α] in
lemma gather {ι : Type} (s : Finset ι) {U : ι → Leaf D α n} {u : ι→ Text α n} (h : ∀ i∈s, Proxy (U i) (u i)) : Proxy (∑ i∈s,U i) (∑ i∈s,u i) := by
  induction s using Finset.induction with
  | empty => simp [Proxy.zero]
  | insert i s he ih => simpa only [Finset.sum_insert he] using (h i (Finset.mem_insert_self ..)).plus (ih fun a ha=> h a (Finset.mem_insert_of_mem ha))
omit [Fintype α] in
lemma reindex (h : Proxy U u) (e : Fin n≃Fin m) : Proxy (fun i=>escort e (U i)) (escort e u) := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; exact ⟨x,A,hx,fun i=>escort e (f i),tendsto_pi_nhds.mpr fun v=>tendsto_pi_nhds.mp H (v ∘ e), p.mono fun i ⟨l,r,s⟩=>⟨l.reindex e,r.reindex e,s.reindex e⟩⟩
omit [Fintype α] in
lemma polished (h : Proxy U u) : Proxy (fun i=> polish (U i)) (polish u) := by
  apply Proxy.eq ((gather _ (fun v (_: v∈ (Finset.univ : Finset _))=> h.reindex v)).scale _)
  exact Eventually.of_forall (fun i=> by simp [polish])

lemma pluck_passage {u : Text α (n+1)} {F : ℕ→ Text α (n+1)} (he : Tendsto F atTop (𝓝 u))
    (hv : ∀ᶠ i in atTop, Within (lawn α) σ p (F i)) (hp : 0<σ) (hn : n ≠ 0) : Tendsto (fun i=> pluck (F i)) atTop (𝓝 (pluck u)) := by
  refine tendsto_pi_nhds.mpr fun v=> ?_
  let j : Fin n:=⟨0,by omega⟩
  apply tendsto_tsum_of_dominated_convergence ((expo_one hp (v j)).mul_left p) (fun z=> (tendsto_pi_nhds.mp he (hitch z v))) (hv.mono (fun a ha z=>?_))
  apply (item_bound ha j.succ (hitch z v)).trans
  rw [hitch_succ,run_some]; apply mul_le_mul_of_nonneg_left ?_ ha.1
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (run_nonneg ..)) (neg_nonpos.mpr hp.le))
lemma plucked {u : Text α (n+1)} {U : Leaf D α (n+1)} (h : Proxy U u) (hn : n ≠ 0) : Proxy (fun i=> pluck (U i)) (pluck u) := by
  obtain ⟨x,A,hx,f,H,p⟩:= h
  exact ⟨x,A,hx,fun i=> pluck (f i), pluck_passage H (p.mono fun i hi=>hi.2.1) hx hn, p.mono fun i ⟨l,r,s⟩=>⟨l.plucked,r.plucked hx.le,s.pluck r hx.le⟩⟩
omit [Fintype α] in
lemma sewn {u : Text α (n+1)} {U : Leaf D α (n+1)} {v : Text α (k+1)} {V : Leaf D α (k+1)}
    (h : Proxy U u) (hv : Proxy V v) : Proxy (fun i=> seam (U i) (V i)) (seam u v) := by
  obtain ⟨x,A,hx,f,H,p⟩:= h; obtain ⟨z,B,hz,g,H',q⟩:= hv
  let α₀ := min x z
  let η : ℝ := min (α₀/(k+1)) (α₀/(n+1))
  have ht : 0 < α₀:= lt_min hx hz
  have hw : 0 < η:=lt_min (by positivity) (by positivity)
  have hu : (k+1)*η≤α₀:= by rw [mul_comm]; exact (le_div_iff₀ (by positivity : (0:ℝ) < k+1)).mp (min_le_left ..)
  have hy : (n+1)*η≤α₀:= by rw [mul_comm]; exact (le_div_iff₀ (by positivity : (0:ℝ) < n+1)).mp (min_le_right ..)
  exact ⟨η,A*B, hw, fun i=> seam (f i) (g i), tendsto_pi_nhds.mpr fun a=> (tendsto_pi_nhds.mp H (hitch (a 0) (snip n k (crop a)))).mul (tendsto_pi_nhds.mp H' (hitch (a 0) (keep n k (crop a)))), (p.and q).mono fun i ⟨⟨l,r,s⟩,⟨l',r',s'⟩⟩=>
    ⟨l.sewn l', (r.mono (min_le_left ..) le_rfl).sewn (r'.mono (min_le_right ..) le_rfl) hw.le hu hy,s.sewn s' l l' r r' hx.le hz.le⟩⟩
end Proxy
end YM.WilsonBulk.Sheet
