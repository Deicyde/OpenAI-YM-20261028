import YM.MergeProof.West.Peak
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Sharp
open Filter Set Function MeasureTheory Analysis Extraction Table Ward MergeProof.Ribbons MergeProof Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
open Extraction.Gaps Extraction.Spin
variable {p k N m:ℕ} {ε:ℝ} (hε:0<ε)
include hε
lemma expanding (H : CellHyp C F) (x : C.book.Token) :
    ∀ᶠ m in atTop,F.late (centeredBudget C x (Real.exp (((x.1:ℝ)+2*ε)*C.S.scale m)) m) := by
  rcases x with ⟨d,v⟩
  obtain ⟨m₀,hp,A,hA,η⟩ := H.centered d ε (‖v‖+1) hε (by positivity)
  let e:ℝ:= -(d:ℝ)-ε; let w i:=C.S.a i^e
  have hh: Note C.S (fun i=>(A+1)*w i) (0+e*(-1)):= (Note.notes C.S _ (by linarith :0<A+1)).mills ((Note.note_a C.S).powr e)
  have he: e≤0:=by dsimp [e]; linarith [Nat.cast_nonneg (α:=ℝ) d]
  filter_upwards [eventually_ge_atTop m₀,hh.outweigh (Note.bell_exp C.S ((d:ℝ)+2*ε)) (by unfold e; linarith),C.S.shrinks.eventually (ge_mem_nhds (α:=ℝ) (by norm_num : (0:ℝ) < 1))] with m hm hh hx
  apply (η _ hm 1 (by norm_num)).mono
  intro i hi; refine hi.mono fun j hj => ?_
  obtain ⟨h,hj⟩ := hj; refine ⟨h,hp.trans (hm.trans h),fun o => ⟨(hj v (by simp) o).1,(hj v (by simp) o).2.trans (?_)⟩ ⟩
  refine le_trans ?_ hh; rw [add_mul,one_mul]
  exact add_le_add_right (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (C.S.a_pos _) hx he) _

lemma spectra {v:Fin n→ C.book.Token} (H: CellHyp C F):∀ᶠ m in atTop, ∀ᶠ u:ℕ×ℕ in F.fuse, m≤u.1∧∀ i j, centeredBudget C (Extraction.Spin.token C.book (v i) j) (Real.exp ((((v i).1:ℝ)+2*ε)*C.S.scale m)) m u.1 u.2 ∧ Fit (Extraction.Spin.token C.book (v i) j) m u.1 u.2:=by
  let T := fun i : Fin n × Extraction.Spin.Frame => Extraction.Spin.token C.book (v i.1) i.2
  filter_upwards [eventually_all.mpr (fun i => expanding hε H (T i))] with k hk
  have ht : ∀ᶠ u:ℕ×ℕ in F.fuse, ∀ i,centeredBudget C (T i) (Real.exp ((((T i).1:ℝ)+2*ε)*C.S.scale k)) k u.1 u.2:= eventually_all.mpr fun i=> hk i
  have he : ∀ᶠ u in F.fuse, ∀ i, Around.Fit (T i) k u.1 u.2 := eventually_all.mpr fun i => by
    rw [Extraction.Order.fused]; exact Eventually.of_forall fun r => (Around.fit (f:=F) (T i) k).mono fun p hp => hp _
  filter_upwards [ht,he,large_mesh F k] with u h hp hv
  refine ⟨hv,fun i j=>⟨?_,hp (i,j)⟩⟩
  have hx : (T (i,j)).1=(v i).1:= by dsimp [T,Extraction.Spin.token]; split <;> rfl
  specialize h (i,j); rw [hx] at h;exact h
include hC hq ho H hε
def honor (S:Schedule) (u:Fin n→C.book.Token)(ε:ℝ)(k:ℕ):=∏ i:Fin n, Real.exp ((((u i).1:ℝ)+2*ε)*S.scale k)
-- use C.book linear tags
lemma maine {q:Fin n→S.Tag} (l:ℕ) (hw:(n:ℝ)*6<(l:ℝ)) :∀ᶠ m in atTop, ∀ x, slide C.S m x→ ‖disc q x‖ ≤ honor C.S (expose ∘ q) ε (m+l):=by
    let w : Fin n→ C.book.Token := expose ∘ q
    filter_upwards [(tendsto_add_atTop_nat l).eventually (spectra hε (v:=w) hq)] with m hm x hs
    apply le_of_tendsto_of_frequently (x:=𝓝 x) ((cont_disc H q (slide_conf C.S x hs)).continuousAt.norm)
    refine (((meets_grid C x).and_eventually (show ∀ᶠ y in 𝓝 x,slide C.S m y from (slide_open C.S m n).mem_nhds hs)).mono ?_)
    rintro y ⟨⟨hy,j,a,rfl⟩,hh⟩
    let y:=Extraction.Order.grid C j a; let I:= {i:Fin n×Fin n//i.1≠i.2}; let d:= m+l
    have ht : Tendsto (fun i:ℕ×ℕ=> C.numeric i.1 i.2 w (Cells.location C.S j i.1 i.2 ∘ a)) F.fuse (𝓝 (disc q y)) := by
       have ht:= Extraction.Order.along (Cells.eventual_grid (k:=j) C F S ho a hy w)
       exact ht
    change ‖disc q _‖ ≤ _; apply le_of_tendsto ht.norm
    have he (i:I): ∃ b:Axis, C.S.a m < |distances y i.val.1 i.val.2 b|:=by
        have hp := above_coord (C.S.a m) (y i.val.2-y i.val.1) (hh i.val.1 i.val.2 i.property); exact hp
    choose b hb using he
    obtain ⟨r,hr,hQ⟩:= ((show ∀ᶠ r in 𝓝[>] (C.S.a m),C.S.a m < r from self_mem_nhdsWithin).and (eventually_all.mpr fun i:I=> (show ∀ᶠ r in 𝓝[>] (C.S.a m), r ≤ |distances y i.val.1 i.val.2 (b i)| from mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (hb i))))).exists -- fix
    have hp : ∀ᶠ i:ℕ×ℕ in F.fuse, ∀ x∈({y}:Set _), someFine C.S i.2 r x := by
       rw [Extraction.Order.fused,Extraction.Order.late]
       filter_upwards [F.per.cofinal.eventually (expand_equivalent C.S (isCompact_singleton (x:=y)))] with p hp
       apply Eventually.of_forall; intro N x hx k l hk
       obtain rfl : x=y:= hx; let u:I:=⟨(k,l),hk⟩
       exact ⟨b u,fun t=>(hQ u).trans (hp _ (mem_singleton _) k l (b u) t)⟩
    filter_upwards [hp,large_mesh F j,hm] with i hi hj h'
    let a':=pushSite C.S hj ∘ a
    have hP (t:Fin n): wrap (C.side i.1 i.2) (a' t)= Cells.location C.S j i.1 i.2 (a t):=by
        rw [Cells.location,dif_pos hj,Ratio.embed_wrap]; rfl
    have hz:tag (C.S.a i.1) a'=y:=by
       ext1 t; exact finer ..
    change ‖C.numeric _ _ w _‖ ≤ _; rw [show (Cells.location C.S j i.1 i.2 ∘ a)=(wrap _ ∘ a') from (funext hP).symm]
    refine contour hC w {y} r hi _ hr (Nat.le_add_right m l) ?_ h' a' hz
    have ht := mul_lt_mul_of_pos_right hw (C.S.a_pos (m+l))
    linarith [fur l m C.S,C.S.a_pos (m+l)]
def tagWeights (q:Fin n→S.Tag):ℕ:=∑ i:Fin n, (q i).1
variable {q:Fin n→S.Tag}
omit hC hq ho H hε in
lemma honor_eq (k): honor C.S (expose∘q) ε k=Real.exp (((tagWeights q:ℝ) + n * (2*ε))*C.S.scale k):=by
     unfold honor tagWeights
     rw [← Real.exp_sum,← Finset.sum_mul]
     change Real.exp ((∑ i:Fin n, (↑(q i).1+2*ε : ℝ)) * C.S.scale k) = _
     simp [Finset.sum_add_distrib]

/-- Actual continuum separated kernel bound from the same seed/cutoff hierarchy (global all arities at a common min gap). -/
lemma separatedPower:∃ A:ℝ,0<A∧∀ (r:ℝ),0 < r → r ≤ 1 → ∀ x:Points n, (∀ i j:Fin n, i≠j → r ≤ ‖x j-x i‖) → ‖disc q x‖ ≤ A*r^(-(tagWeights q:ℝ)-ε):=by
    obtain ⟨l,hl⟩ := exists_nat_gt ((n:ℝ)*6)
    let δ := ε/ (4*((n:ℝ)+1)); have hn := (show 0≤(n:ℝ) by exact Nat.cast_nonneg _); let p := (tagWeights q:ℝ)+ε
    have hp: 0 < p := by dsimp [p]; positivity
    have hd': 0<(4:ℝ)*(n+1):=by linarith
    have hd: 0 < δ := div_pos hε hd'
    let e := (tagWeights q:ℝ)+n*(2*δ)
    have he:e < p := by
        suffices (n:ℝ)*(2*δ)<ε by dsimp [e,p]; linarith
        dsimp only [δ]; rw [show (n:ℝ)*(2*(ε/(4*(n+1))))=(n*2*ε)/(4*(n+1)) from by ring]
        exact (div_lt_iff₀ hd').mpr (by nlinarith)
    have hh:Note C.S (fun m=> honor C.S (expose∘q) δ (m+1+l)) e:=by
        conv => arg 2; intro m; rw [honor_eq (q:=q),show m+1+l=m+(l+1) from by omega]
        exact Note.longer (C:=C) (Note.bell_exp C.S _) _
    have hw:Note C.S (fun m=> (4*C.S.a m)^(-p)) p := (Note.powr (Note.mills (Note.notes C.S (4:ℝ) (by norm_num)) (Note.note_a _)) (-p)).swapP (by ring)
    obtain ⟨M,hM⟩:= eventually_atTop.1 ((hh.outweigh hw he).and (maine hC hq ho H hd l hl (q:=q)))
    let A:= 1+honor C.S (expose∘q) δ (M+l); have ha:1≤A:=by dsimp [A]; rw [honor_eq (q:=q)]; linarith [Real.exp_pos (e*C.S.scale (M+l))]
    refine ⟨A,ha.trans_lt' (by norm_num),fun r hr hr' x hx=>?_⟩
    have hpr:0<r^(-p):= Real.rpow_pos_of_pos hr _
    have hc:= Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr' (neg_nonpos.mpr hp.le)
    by_cases hy: r ≤ 4*C.S.a M
    · have hf: ∃ j:ℕ, 4*C.S.a j < r:=by
          have ht:= ((C.S.shrinks.const_mul (4:ℝ)).eventually (gt_mem_nhds (by simpa only [mul_zero] using hr)))
          exact ht.exists
      let z:= Nat.find hf; have hz : 4*C.S.a z < r := Nat.find_spec hf
      have hMz: M < z:=by_contra fun h=> by
          linarith [C.S.strictAnti.antitone (le_of_not_gt h)]
      have he' : ∃ j, z=j+1 := ⟨z-1, (Nat.sub_add_cancel (show z≥1 from by omega)).symm⟩
      obtain ⟨j,hj⟩ := he'; rw [hj] at hz
      have hrj:r≤4*C.S.a j:= le_of_not_gt (Nat.find_min hf (by show j<z; omega))
      calc ‖disc q x‖ ≤ honor C.S (expose∘q) δ (j+1+l) := (hM (j+1) (by omega)).2 _ fun i i' hi=>hz.trans_le (hx i i' hi)
           _ ≤ _:= le_trans ((hM j (by omega)).1.trans (Real.rpow_le_rpow_of_nonpos hr hrj (neg_nonpos.mpr hp.le))) (by change r^(-p)≤A*r^(-(tagWeights q:ℝ)-ε); simpa only [p,one_mul,sub_eq_add_neg,neg_add] using (mul_le_mul_of_nonneg_right ha hpr.le))
    calc ‖disc q x‖ ≤ honor C.S (expose∘q) δ (M+l):= (hM M le_rfl).2 _ fun i j hi=>(lt_of_not_ge hy).trans_le (hx i j hi)
         _ ≤ _ := by dsimp only [p] at hc;rw [neg_add] at hc;rw [sub_eq_add_neg];exact le_trans (by linarith : honor C.S (expose∘q) δ (M+l) ≤ A) (le_mul_of_one_le_right (by linarith) hc)
end YM.MultipleContact.Sharp
