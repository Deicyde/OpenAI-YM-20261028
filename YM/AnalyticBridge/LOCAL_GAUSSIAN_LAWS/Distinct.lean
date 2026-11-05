import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Geometry

/-!
# The windows really are different (even after delay)

End but NOT mid, at actual usable non-tree addresses, every odd L≥21,
any B≥20 and all large periods. Take two crossings along axis k at
blocks dist floor(B/20) along axis i (so END accepts, including the
pairwise comparison of ends). Put them at opposite *within block*
extremes of the i-offset. MID sees those offsets even for crossings. All
colors intact. Can specialize at B=radiusB x, no-hole.

This is a theorem about GEOMETRY, not a theorem that every positive
binit/cut precision then detects the distinction in its symmetrized
covariance (e.g. one would still have to check specific nonzero
couplings per gauge, and identity Q doesn't detect it). This geometry result *is* our
negative test at the interface level, to show why a purely
address-type/positivity argument couldn't license that bigger shortcut.
We use no nonequality assumption when pricing the change.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Stores YM.Bid Next SectorChange
  Rows Wisps Gaussian Function Set FreeResolvent Matrix
open scoped Classical BigOperators

section geometry
variable {c f n : Side} {S : StepData c f} {G : Gauge}
private lemma cover_step_two (i k : Axis) (e : ℤ) (d : ℕ) (h : e.natAbs ≤ 1) (hi : i ≠ k) (hd : 0 < d) :
    ∀ u : Axis, ((d • step i + e • step k : Cover) u).natAbs ≤ d := by
  intro u
  by_cases H : u=i
  · subst u
    simp [nsmul_eq_mul,zsmul_eq_mul,hi]
  by_cases He : u=k
  · subst u; simpa [zsmul_eq_mul,H] using h.trans hd
  simp [step_apply,H,He]

private lemma separated (i k : Axis) (e : ℤ) (d : ℕ) (h : e.natAbs ≤ 1) (hi : i ≠ k) (hd : 0 < d) (hc : 2*d < n.val) :
    pdist (wrap n (d • step i+e • step k)) ≤ d := by
  let v : Cover := d • step i+e • step k
  have hh z := cover_step_two i k e d h hi hd z
  have hl : lift (wrap n v)=v := lift_eq_iff.mpr ⟨rfl,fun u => by
    have hx : (v u).natAbs ≤ d := hh u
    omega⟩
  unfold pdist; rw [hl]; exact Finset.sup_le fun u _ => hh u

private lemma separated_shift (i k : Axis) (d : ℕ) (x y : Cover) (p q : ℤ)
    (h : (q-p).natAbs ≤ 1) (e : y=x+d • step i) (hi : i≠k) (hd : 0<d) (hc : 2*d < n.val) :
    separation (wrap n (x + p • step k)) (wrap n (y + q • step k)) ≤ d := by
  rw [separation_comm,separation, ← map_sub,e,show (x+d • _ + q • step k)-(x+p • step k : Cover)=d • step i+(q-p) • step k from ?_]
  · exact separated _ _ _ _ h hi hd hc
  -- rewrite placeholder ambiguous? 
  rw [sub_smul]; abel

/-- Crossings always retained as free, regardless of forest tags. -/
private lemma retained_cross (S : StepData c f) (F : Forest S.ratio) (x : Bond f)
    (h : S.ratio.parent x.1≠S.ratio.parent (x.1+step x.2)) : x∉F.trunks := fun he => h (F.trunk_internal he).symm

def bareStores (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩
lemma notChilled (S : StepData c f) (F : Forest S.ratio) (x : ℝ) (i : F.Free) : ¬chill (bareStores S) x F i := by
  simp [chill,Stores.dome,Stores.place,halo_spec,bareStores]

private lemma on_block (i k : Axis) (L : Side) {a b : ℤ} (h : Odd L.val) (ha : a.natAbs ≤ L.val/2) (hb : b.natAbs ≤ L.val/2) (hi : i ≠ k) :
    lift (wrap L (a • step i+b • step k)) = a • step i + b • step k := by
  apply lift_eq_iff.mpr ⟨rfl,?_⟩
  intro j
  change _ < 2 * (a*(step i:Cover) j+b*(step k:Cover) j) ∧ 2 * (a*(step i:Cover) j+b*(step k:Cover) j) ≤ _
  obtain ⟨m,hm⟩ := h
  by_cases hj : j=i
  · subst j; simp only [step_apply,if_pos,hi,if_neg,not_false_eq_true,mul_one,mul_zero,add_zero]; omega
  by_cases hh : j=k
  · subst j; simp only [step_apply,if_pos,hj,if_neg,not_false_eq_true,mul_one,mul_zero,zero_add]; omega
  simp [step_apply,hj,hh]

private def crossing (S : StepData c f) (v : Cover) (q : ℤ) (i k : Axis) : Bond f :=
    (S.ratio.embed (wrap c v)+wrap f (q • step i + ((S.patch.L.val/2 : ℕ):ℤ) • step k),k)

private lemma crossing_props (S : StepData c f) (v : Cover) (q : ℤ) {i k : Axis} (he : i≠k) (hq : q.natAbs ≤ S.patch.L.val/2) :
    let g := S.ratio; let e := crossing S v q i k
    g.parent e.1=wrap c v ∧ g.parent (e.1+step k)=wrap c v+step k := by
  intro g e
  let L := S.patch.L; let p : ℤ := (L.val/2:ℕ); let u : Cover := q • step i + p • step k
  have hp : p.natAbs ≤ L.val/2 := by unfold p; omega
  have hh := on_block i k L S.patch.odd_side hq hp he
  have h : e.1 = g.assemble (wrap c v,wrap L u) := by
    unfold e crossing; dsimp only
    unfold Ratio.assemble; dsimp only; exact congr_arg (fun a => g.embed _+wrap f a) hh.symm
  rw [h,g.assemble_parent,Ratio.parents_hop g S.patch.odd_side,g.assemble_res,g.assemble_parent]; dsimp only; erw [hh]
  rw [Pi.add_apply,Pi.smul_apply,Pi.smul_apply]; have he' : p=((g.count.val/2:ℕ):ℤ) := rfl
  refine ⟨rfl,if_pos ?_⟩; change q*step i k+p*step k k=_; rw [step_apply,if_neg (Ne.symm he),step_apply,if_pos rfl,mul_one,mul_zero,zero_add]; exact he'

private lemma axis_cover (S : StepData c f) (v : Cover) (q : ℤ) (i k : Axis) :
    let _g := Mid.double f
    Mid.axis (crossing S v q i k) =
      wrap _ (2 • (((S.patch.L.val:ℕ) • v) + q • step i + ((S.patch.L.val/2:ℕ):ℤ) • step k) + step k) := by
  intro _g; unfold Mid.axis crossing
  dsimp only
  rw [Ratio.embed_wrap, ← map_add, Ratio.embed_wrap, map_add, wrap_step, add_assoc (S.patch.L.val • v)]
  rfl

set_option maxHeartbeats 600000 in
/-- Exact witness: even if posing only on actual active indices of the
no-hole sector, ordered cut geometries aren't universally equivalent. -/
theorem active_discrepancy (S : StepData c f) (G : Gauge) (j : G.ColorIndex) (B : ℕ) (F : Forest S.ratio)
    (x : ℝ) (hb : 20 ≤ B) (hl : 21 ≤ S.patch.L.val) (hc : 2*(B/20+2) < c.val) :
    endSets S B (bareStores S) F x G ≠ midSets S B (bareStores S) F x G := by
  let i : Axis := 0; let k : Axis := 1
  have hi : i≠k := by decide +revert
  let d := B/20
  let L := S.patch.L; let p : ℤ := (L.val/2:ℕ)
  let a := crossing S 0 (-p) i k; let b := crossing S (d • step i) p i k
  have hp : p.natAbs ≤ L.val/2 := by unfold p; omega
  have ha := crossing_props S 0 (-p) hi (show (-p).natAbs ≤ _ from (by rwa [Int.natAbs_neg]))
  have H := crossing_props S (d • step i) p hi hp
  have hw (u : Site c) : u+step k≠u := by
    haveI : Fact (1 < c.val) := ⟨by omega⟩
    intro h
    have he : (step k : Site c)=0 := add_left_cancel (h.trans (add_zero _).symm)
    have hg : (1:ZMod c.val)=0 := by simpa using congr_fun he k
    exact one_ne_zero hg
  let A : F.Free := ⟨a,retained_cross _ F _ (by rw [ha.1,show a.2=k from rfl,ha.2]; exact (hw _).symm)⟩
  let C : F.Free := ⟨b,retained_cross _ F _ (by rw [H.1,show b.2=k from rfl,H.2]; exact (hw _).symm)⟩
  let t : In x (bareStores S) F (G:=G) := (⟨A,notChilled S F x A⟩,j)
  let v : In x (bareStores S) F (G:=G) := (⟨C,notChilled S F x C⟩,j)
  intro he
  have hx : endMeet S B a b ↔ midMeet S B a b := (Set.ext_iff.mp (congr_fun he t)) v
  suffices h : endMeet S B a b ∧ ¬midMeet S B a b from h.2 (hx.mp h.1)
  have hd : 0<d := by unfold d; omega
  constructor
  · have hh (v w : Cover) (g h : ℤ) (hh' : (h-g).natAbs ≤ 1) (hw : w=v+d • step i) := separated_shift (n:=c) i k d v w g h hh' hw hi hd (show 2*d < c.val by unfold d; omega)
    unfold endMeet SectorChange.points
    rw [ha.1,show a.2=k from rfl,ha.2,H.1,show b.2=k from rfl,H.2]
    simp only [Set.forall_mem_insert,Set.mem_singleton_iff,forall_eq,map_zero]
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · simpa only [map_zero,map_add,one_smul,wrap_step,zero_smul,zero_add,add_zero] using! hh 0 (d • step i) 0 0 (by norm_num) (by simp)
    · simpa only [map_zero,map_add,one_smul,wrap_step,zero_smul,zero_add,add_zero] using! hh 0 (d • step i) 0 1 (by norm_num) (by simp)
    · simpa only [map_zero,map_add,one_smul,wrap_step,zero_smul,zero_add,add_zero] using! hh 0 (d • step i) 1 0 (by norm_num) (by simp)
    simpa only [map_zero,map_add,one_smul,wrap_step,zero_smul,zero_add,add_zero] using! hh 0 (d • step i) 1 1 (by norm_num) (by simp)
  intro H'
  let U := 2*(L.val*d+(L.val-1))
  have h : 2*L.val*B < 20*U := by
    have h₀ : B ≤ 20*d+19 := by omega
    have h' := Nat.mul_le_mul_left (2*L.val) h₀
    have hv : L.val-1+1=L.val := by unfold L; omega
    unfold U; change 21 ≤ L.val at hl; nlinarith
  apply h.not_ge; apply le_trans _ H'
  apply Nat.mul_le_mul_left
  rw [separation_comm]
  apply le_trans _ (component_le (Mid.axis b - Mid.axis a) i)
  rw [show Mid.axis b - Mid.axis a=wrap (f*2) (U • step i) from ?_]
  · have hU : 2*U < (f*2).val := by
      rw [show (f*2:Side).val=f.val*2 from rfl,S.sizes]
      have he : (2*(d+2)+1)*L.val ≤ c.val*L.val := Nat.mul_le_mul_right L.val (show _ ≤ c.val from hc)
      have hv : L.val-1+1=L.val := by unfold L; omega
      change 2*(2*(L.val*d+(L.val-1))) < ↑c * L.val * _
      change 21≤L.val at hl; nlinarith [S.patch.L.property]
    have hu : lift (wrap (f*2) (U • step i))=U • step i := lift_eq_iff.mpr ⟨rfl,fun u => by
      have hh := (f*2:Side).property
      by_cases he : u=i
      · subst u; change _ < 2*((U:ℤ)*step i i) ∧ 2*((U:ℤ)*step i i) ≤ _; simp only [step_apply,if_pos,mul_one]; omega
      simp [step_apply,he]⟩
    rw [hu]; simp
  · unfold a b; rw [axis_cover,axis_cover, ← map_sub]
    apply congr_arg (wrap (f*2)); funext u
    obtain ⟨p',hp'⟩ := S.patch.odd_side
    change L.val=2*p'+1 at hp'
    have hU : L.val-1=p'+p' := by omega
    have hh : p=(p':ℤ) := by unfold p; omega
    by_cases he : u=i <;> by_cases H : u=k
    · exact (hi (he.symm.trans H)).elim
    all_goals simp [Pi.smul_apply,nsmul_eq_mul,zsmul_eq_mul,he,H,hh,hi,Ne.symm hi]
    -- i component Nat subtraction
    unfold U; rw [hU]; push_cast; ring
end geometry
end YM.AnalyticBridge.LocalGaussianLaws
