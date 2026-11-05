import YM.Contacts.Solstice.JetLocal
/-!
# One gradual system of thresholds at all arities

With *strict coherence* of the projection, lowering through any fixed grade horizon loses
nothing: the associated readings already agree row by row. Need only ensure apertures &
qualification for when using a larger projected weight itself, and local finiteness away from the
shrinking end. All projections at length in question themselves can thus be finitely integrated
when their tested geometry has paid the proper stage. Use also with fixed length not reading outside
the main horizon. Extra conditions in later parts (PT orders etc.) may use a **single** slower set
of thresholds for more requests; no assertions here that conditions for PT comparison are met.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{Z:Final C F S}
variable (M : Devices Z.sector.derivatives)

-- for any exhausted fixed-size factor applied to root scale, includes even neighboring requests if demanded. Use slow construction below.
structure Thresholds (M : Devices Z.sector.derivatives) where
   time : ℕ → ℝ
   early n : 0< time n
   separates n : 4*time (n+1)< time n
   takes_off : Tendsto time atTop (𝓝 0)
   cost (n:ℕ) : 2*(n+1:ℝ)*time n≤ M.clearance n

lemma installs {f : ℕ→ℝ}(hf : ∀ i,0<f i): ∃ T : Thresholds M, ∀ i,T.time i ≤ f i:= by
   let g(i:ℕ):= min (min (f i) (dyad i)) (M.clearance i/(2*(i+1:ℝ))); let b : ℕ→ℝ := fun n=> Nat.rec (g 0) (fun i r=>min (r/8) (g (i+1))) n; have hx i:b (i+1)= min (b i / 8) (g (i+1)) := rfl; have hg(i:ℕ): 0<g i:=by refine lt_min (lt_min (hf i) (dyad_pos i)) (div_pos (M.clearance_pos i) (by positivity));
   have hp(i):0< b i:=by induction i; exact hg 0; rename_i i hi; exact lt_min (div_pos hi (by norm_num)) (hg _)
   have he(i): b i ≤ g i:= by cases i; exact le_rfl; rename_i i; exact min_le_right ..
   refine ⟨⟨b,hp, fun i=> ?_, squeeze_zero (fun i=>(hp i).le) (fun i=>(he i).trans ((min_le_left ..).trans (min_le_right ..))) dyad_shrivels,fun i=>?_⟩,fun i=> (he i).trans ((min_le_left ..).trans (min_le_left ..))⟩
   · linarith only [show b (i+1) ≤ b i/8 from min_le_left .., hp i]
   have ht:= (le_div_iff₀ (show 0<(2:ℝ)*(i+1:ℝ) by positivity)).mp ((he i).trans (min_le_right ..)); linarith only [ht]

variable {M}
namespace Thresholds
variable (T : Thresholds M)

lemma antitone : Antitone T.time:= antitone_nat_of_succ_le fun i=> by linarith only [T.separates i,T.early (i+1)]
def gate (n : ℕ)(x : ℝ) := if n=0 then 1 else cutoff (T.time n) x
lemma smooth (n : ℕ) : ContDiff ℝ ∞ (T.gate n):=by
    by_cases h:n=0; rw [show T.gate n=(fun _ : ℝ=> (1:ℝ)) from funext (fun x=> if_pos h)]; exact contDiff_const
    rw [show T.gate n=(fun x => cutoff (T.time n) x) from funext (fun x=> if_neg h)]; apply cutoff_smooth
lemma fate (n x): T.gate n x∈ Icc 0 1:= by
    by_cases he:n=0; rw [gate,if_pos he]; exact ⟨zero_le_one,le_rfl⟩
    rw [gate,if_neg he]; exact cutoff_mem ..
@[simp] lemma base (x) : T.gate 0 x=1:= if_pos rfl
lemma turns (n : ℕ){x:ℝ}(hx:0≤x)(hh:x ≤ T.time n) : T.gate n x=1:= by unfold gate; split; rfl; exact cutoff_eq_one (T.early n) (by rwa [Real.norm_of_nonneg hx])
lemma active {v:ℕ} (hv:v≠0) {x:ℝ}(hx:0≤x)(he:T.gate v x≠0): x< 2*T.time v:= by
    by_contra! h; apply he; rw [gate,if_neg hv]; apply cutoff_eq_zero (T.early v); rwa [Real.norm_of_nonneg hx]
lemma local_clock (n : ℕ) {k : ℕ} (hh : n<k){x:ℝ}(hx:0 ≤ x)(he:T.gate k x≠0): T.gate n x=1:= T.turns _ hx (by linarith only [T.active (by omega:k≠0) hx he,T.antitone hh,T.separates n,T.early (n+1)]) -- anti `hh` le n+1 k? Lean



def Cap (x : ℝ)(n : ℕ) := ∀ i > n, T.gate i x=0
lemma finite (x:ℝ)(hx: 0<x) : ∃ i:ℕ, ∀ᶠ y in 𝓝 x, T.Cap y i:= by
   obtain ⟨N,hN⟩:= eventually_atTop.mp (T.takes_off.eventually (p:=fun t=>t<x/4) (gt_mem_nhds (by positivity))); refine ⟨N,?_⟩; filter_upwards [lt_mem_nhds (show x/2<x from half_lt_self hx)] with y hy i hi; by_contra h; have hh:=T.active (by omega : i≠0) ((half_pos hx).trans hy|>.le) h; linarith only [hh, hy,hN i hi.le]
def enter (x : ℝ) : ℕ:= if h:0<x then Nat.find (Exists.imp (fun _ h=>h.self_of_nhds) (T.finite x h)) else 0
lemma enters (x:ℝ)(hx:0<x): T.Cap x (T.enter x):= by rw [enter, dif_pos hx]; apply Nat.find_spec
lemma parked {x:ℝ}(hx:0<x): T.gate (T.enter x) x≠0:= by
    by_contra h; cases he:T.enter x with
    | zero=>rw [he,base] at h; exact one_ne_zero h
    | succ n=>
      have hT:T.Cap x n:=by
         intro i hi; by_cases h':i=n+1; rw [← he] at h'; exact h' ▸ h
         apply T.enters x hx; omega
      have hh:T.enter x≤n:=by rw [enter,dif_pos hx]; exact Nat.find_min' _ hT
      omega
lemma eventually_sees (n : ℕ) : ∀ᶠ x:ℝ in 𝓝[>] 0,T.gate n x=1:= by filter_upwards [eventually_mem_nhdsWithin, (show ∀ᶠ x:ℝ in 𝓝[>] 0,x≤T.time n from Eventually.filter_mono nhdsWithin_le_nhds (ge_mem_nhds (T.early n)))] with x hx ht using T.turns n (le_of_lt (show 0<x from hx)) ht
lemma enters_more : Tendsto T.enter (𝓝[>] 0) atTop:= tendsto_atTop.mpr (fun i=> by
    filter_upwards [T.eventually_sees i,self_mem_nhdsWithin (a:=(0:ℝ)) (s:= Ioi 0)] with x hx he; by_contra! h; exact zero_ne_one ((T.enters _ he _ h).symm.trans hx))
lemma funded {k : ℕ} {x:ℝ}(hx:0<x) (hk:k>0) (h : k≤ T.enter x) : (k:ℝ)*x ≤ M.clearance k:= by
    have he: T.gate k x≠0:= by
      rcases h.eq_or_lt with h|h; rw [h]; exact T.parked hx
      rw [local_clock T _ h hx.le (T.parked hx)]; exact one_ne_zero
    apply le_trans _ (T.cost k); have hx:= T.active hk.ne' hx.le he; have hk':0<(k:ℝ):=by exact_mod_cast hk
    linarith only [T.early k,mul_lt_mul_of_pos_left hx hk']
/-- catch any fixed multiple of external scale in the collar of the highest branch comparator. -/
lemma ripe (C:ℝ) : ∀ᶠ x:ℝ in 𝓝[>] 0,C*x ≤ M.clearance (T.enter x) := by
   obtain ⟨i:ℕ ,hi⟩:= exists_nat_gt (max C 0); -- I fix
   filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),T.enters_more.eventually_ge_atTop i] with x hx hT; have he:0<x:= hx; have hp: (i:ℝ)≤ T.enter x:=by exact_mod_cast hT
   exact le_trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (hi.le.trans hp)) he.le) (T.funded he (by exact_mod_cast ((lt_of_le_of_lt (le_max_right ..) hi).trans_le hp : (0:ℝ)< T.enter x)) le_rfl)

-- exact gated projection, as stated in graded coordinates. No polynomial-log comparison here.
def activeRow (n : ℕ)(s:ℝ) (x:E4) := ((T.gate n s:ℝ):ℂ) • M.row x n
def projectSum (s:ℝ)(x:E4) (h:ℕ) := ∑ i∈ Finset.range (h+1), ((T.gate i s:ℝ):ℂ) • M.insertRow x i
def display (s:ℝ)(x:E4) := T.projectSum s x (T.enter s) -- Expression linear map
lemma active_row (n : ℕ) (s:ℝ){x:E4}(h:0<s)(f:Expression Z.sector.derivatives): M.row x n (T.display s x f)= T.activeRow n s x f:= by
   unfold display projectSum; rw [LinearMap.sum_apply,map_sum]; by_cases he : n ≤ T.enter s
   · rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le he))];
     · rw [LinearMap.smul_apply,map_smul,M.row_diagonal]; rfl
     intro k hk hh; rw [LinearMap.smul_apply,map_smul, M.row_other _ n k hh.symm,smul_zero]
   rw [activeRow,T.enters _ h _ (not_le.mp he), Finset.sum_eq_zero, Complex.ofReal_zero,zero_smul,LinearMap.zero_apply] -- fix
   intro i hi; have hh:i≠n:= by have ht:=Finset.mem_range.mp hi; omega
   rw [LinearMap.smul_apply,map_smul,M.row_other _ _ _ hh.symm,smul_zero]
-- projection through any stipulated active horizon agrees EXACTLY, not a possible r^ε mismatch.
lemma expand_to {n : ℕ}{s :ℝ}(hx:0<s)(h : s≤ T.time n)(x : E4)(f:Expression Z.sector.derivatives): M.replaceAt x n (T.display s x f)=M.replaceAt x n f:= by
    rw [← M.replace_sum,← M.replace_sum]; refine Finset.sum_congr rfl fun v _=>?_ ; rw [Devices.insertRow,LinearMap.comp_apply,LinearMap.comp_apply, T.active_row v s hx f, activeRow,T.turns v hx.le (h.trans (T.antitone (Nat.le_of_lt_succ v.isLt))),Complex.ofReal_one,one_smul]
lemma weight_root {k : ℕ} (s:ℝ)(x:E4) : T.projectSum s x (k+1)= T.projectSum s x k+ ((T.gate (k+1) s:ℝ):ℂ) • (M.replaceAt x (k+1)-M.replaceAt x k) := by
    have he:M.insertRow x (k+1)=M.replaceAt x (k+1)-M.replaceAt x k:=by
      apply LinearMap.ext; intro y; rw [LinearMap.sub_apply,← M.replace_sum, ← M.replace_sum x k, Fin.sum_univ_castSucc]; simp only [Fin.val_last,Fin.val_castSucc]; abel -- maybe casts
    unfold projectSum; rw [Finset.sum_range_succ,he]
lemma root_is (s:ℝ)(x:E4): T.projectSum s x 0=M.replaceAt x 0:= by
    apply LinearMap.ext; intro y; rw [projectSum, Finset.sum_range_succ, Finset.sum_range_zero,zero_add,base,Complex.ofReal_one,one_smul,← M.replace_sum]; simp
end Thresholds
end YM.Contacts.Solstice
