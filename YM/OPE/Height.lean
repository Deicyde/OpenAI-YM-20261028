import YM.OPE.Columns.SectorCost

/-!
# Along a layer of log-comparable meshes

No loss of overshoots along stages on this arbitrary path.
Can even take stages at a logarithm o(T), to capture an exterior with no
power cost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Function Set Lattice RG MergeProof
open scoped Topology
variable {ι κ : Type*} {l : Filter ι} {f : Filter κ} {T : ι→ℝ} {a b c : ℝ}
variable {S : Schedule} {m k : ι→ℕ}

structure Height (S : Schedule) (l : Filter ι) (T : ι→ℝ) (m : ι→ℕ) (c : ℝ) : Prop where
    grows : Tendsto m l atTop
    pace : Tendsto (fun i=> S.scale (m i)/T i) l (𝓝 c)

lemma scale_mono (S : Schedule) : StrictMono S.scale:=fun _ _ h=>Real.log_lt_log (inv_pos.mpr (S.a_pos _))
    (inv_lt_inv₀ (S.a_pos _) (S.a_pos _) |>.mpr (S.strictAnti h))
namespace Height
variable (h:Height S l T m a)(hp:Height S l T k b)
include h
lemma step (hh:S.Gentle) : Height S l T (fun i=> m i+1) a:=by
    have hr : RateIs l T (fun i=>S.a (m i+1)) (-1*a):=Columns.rescale (v:=m) ((Ribbons.Note.note_a S).scales hh) h.grows h.pace
    refine ⟨tendsto_atTop_mono (fun i=> Nat.le_succ (m i)) h.grows, ?_⟩; have hx:=hr.rate.neg; simp_rw [← neg_div,neg_mul,one_mul,neg_neg] at hx;
    simpa only [Schedule.scale,Real.log_inv] using hx
lemma earlier (hu:a<b)(hT:Tendsto T l atTop)(hp:Height S l T k b) : ∀ᶠ i in l, m i<k i :=by
    obtain ⟨c,hc,hc'⟩:=exists_between hu
    filter_upwards [(h.pace.eventually (gt_mem_nhds hc)|>.and (hp.pace.eventually (lt_mem_nhds hc'))).mono (fun i ⟨hx,he⟩=>(show S.scale (m i) / T i <S.scale (k i)/T i from lt_trans (show _<c from hx) he)),hT.eventually_gt_atTop 0] with i hi ht
    exact ((scale_mono S).lt_iff_lt).1 (lt_of_mul_lt_mul_right (show S.scale (m i)*(T i)⁻¹ < S.scale (k i)*(T i)⁻¹ from by rw [← div_eq_mul_inv,← div_eq_mul_inv]; exact hi) (inv_pos.mpr ht|>.le))
lemma mesh : RateIs l T (fun i=>S.a (m i)) (-a):= by
    have he:= Columns.rescale (Ribbons.Note.note_a S) h.grows h.pace; rwa [neg_one_mul] at he
lemma comp {r : κ → ι} (he : Tendsto r f l) : Height S f (T ∘ r) (m ∘ r) a:= ⟨h.grows.comp he,h.pace.comp he⟩
lemma nonneg [l.NeBot] (hT:Tendsto T l atTop) : 0 ≤ a:= by
    refine ge_of_tendsto h.pace ?_; filter_upwards [hT.eventually_ge_atTop 0] with i hi using div_nonneg ((S.scale_zero).symm.le.trans ((scale_mono S).monotone (Nat.zero_le _))) hi
end Height
lemma found_up {e:ι→ℝ}(h:Tendsto e l atTop) (hT:Tendsto (fun i=> e i/T i) l (𝓝 a))(S:Schedule)(hp:S.Gentle) : ∃ m : ι→ℕ, Height S l T m a ∧ ∀ i,e i < S.scale (m i):=by
    classical
    have hh (i:ι) := (S.divergent.eventually_gt_atTop (e i)).exists; let m i:=Nat.find (hh i); have hv i:e i< S.scale (m i):= Nat.find_spec (hh i)
    have hy:Tendsto m l atTop:=tendsto_atTop.mpr fun j => by filter_upwards [h.eventually_ge_atTop (S.scale j)] with i hi using ((scale_mono S).le_iff_le.mp (le_trans hi (hv _).le))
    have he (i): 0< m i → S.scale (m i-1) ≤ e i:= by
       intro h; apply le_of_not_gt; intro hl; have ht : m i ≤ m i-1:= Nat.find_min' (hh i) hl; omega
    let p i:=m i-1; have hu:Tendsto p l atTop:=tendsto_atTop.mpr fun i=> by filter_upwards [hy.eventually_gt_atTop i] with j hj; unfold p; omega
    let z i:= S.scale (p i); let u i:= S.scale (m i); have hg:Tendsto (fun i=> u i /z i) l (𝓝 1):=by
       have hz:= (show S.Gentle from hp); unfold Schedule.Gentle at hz; have hF: ∀ᶠ i in l,z i ≠ 0:= ((S.divergent.comp hu).eventually_gt_atTop 0).mono fun i hi=> ne_of_gt hi
       refine (show Tendsto (fun i=> 1+ Real.log (S.block (p i)).val /z i) l (𝓝 1) from by simpa only [add_zero] using! ((hz.comp hu).const_add 1)).congr' ?_
       filter_upwards [hF,hy.eventually_gt_atTop 0] with i hi hx; unfold u; rw [← (show p i+1=m i from Nat.sub_add_cancel hx),S.scale_succ,add_div,div_self hi]
    have hf:Tendsto (fun i=>u i/e i) l (𝓝 1):=by
       refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
       · filter_upwards [h.eventually_gt_atTop 0] with i hi using (one_le_div hi).mpr (hv i).le
       filter_upwards [hy.eventually_gt_atTop 0,(S.divergent.comp hu).eventually_gt_atTop 0,(S.divergent.comp hy).eventually_ge_atTop 0] with i hi hp hu using div_le_div_of_nonneg_left hu hp (he i hi)
    refine ⟨m, ⟨hy,(show Tendsto (fun i=> u i/e i*(e i/T i)) l (𝓝 a) from by simpa only [one_mul] using! hf.mul hT).congr' ?_⟩,hv⟩
    filter_upwards [h.eventually_gt_atTop 0] with i hi; unfold u; field_simp
lemma found {S:Schedule}(hT:Tendsto T l atTop)(hp:S.Gentle)(ha:0 ≤ a) : ∃ m:ι→ℕ, Height S l T m a:=by
    rcases ha.eq_or_lt with ha|ha; subst a
    · let e i:=Real.sqrt (T i); have he:Tendsto e l atTop:= by simp_rw [e,Real.sqrt_eq_rpow]; exact (tendsto_rpow_atTop (by norm_num)).comp hT
      have ht : Tendsto (fun i=>e i/T i) l (𝓝 0):=by
         refine (show Tendsto (fun i=> (e i)⁻¹) l (𝓝 0) from tendsto_inv_atTop_zero.comp he).congr' ?_; filter_upwards [hT.eventually_gt_atTop 0] with i hi; have hf:e i*e i=T i:= Real.mul_self_sqrt hi.le; have hh:0<e i:=Real.sqrt_pos.mpr hi; field_simp; linarith only [hf]
      obtain ⟨m,h,-⟩:= found_up he ht S hp; exact ⟨m,h⟩
    obtain ⟨m,h,-⟩:= found_up (hT.const_mul_atTop ha) (show Tendsto (fun i=> a*T i/T i) l (𝓝 a) from tendsto_const_nhds.congr' ((hT.eventually_gt_atTop 0).mono fun i hi => (mul_div_cancel_right₀ _ hi.ne').symm)) S hp; exact ⟨m,h⟩

lemma RateIs.swap {p:ι→ℝ}(h:RateIs l T p a)(he:a=b) : RateIs l T p b:=he ▸ h
lemma RateIs.overtakes {p q:ι→ℝ}(h:RateIs l T q b)(hh:RateLE l T p a)(hT:Tendsto T l atTop)(hu:a<b):∀ᶠ i in l,p i< q i:=by
    have ht:= (h.mul (RateIs.const (c:=1/2) hT (by norm_num))).outweigh hh (by linarith) hT; filter_upwards [ht,h.pos] with i hi hp
    exact lt_of_le_of_lt ((Real.le_norm_self _).trans hi) (by linarith only [hp])
lemma RateIs.prod {S:Finset κ}{F:κ→ι→ℝ}{b:κ→ℝ}(h:∀ i∈ S,RateIs l T (F i) (b i)) (hT:Tendsto T l atTop):
    RateIs l T (fun i=> ∏ j∈ S,F j i) (∑ j ∈ S,b j):=by
    classical
    induction S using Finset.induction with
    | empty => simpa using RateIs.const (c:=1) hT one_pos
    | insert k s hk IH=> simpa only [Finset.prod_insert hk,Finset.sum_insert hk] using
        (h k (Finset.mem_insert_self ..)).mul (IH (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))
end YM.OPE
