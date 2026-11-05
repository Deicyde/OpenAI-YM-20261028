import YM.PCalc.Band

/-! Nearby real target shooting by residual margins, using the same open top band and same
moves. Not a uniqueness result; `Band` supplies that part only under its quantitative/analytic
hypotheses. This adapts the two boundaries to a nearby level-zero target without resetting the
schedule. -/
noncomputable section
namespace YM.Extension.UV
open Function Filter Set Lattice RG RG.Supply RG.Shoot Wilson Precision Input
open scoped Topology
variable {G : Gauge} {a : Levels G}

def jump (a : Levels G) (i : ℕ) := G.slopeConstant * Real.log (a.S.block i).val
def margin (a : Levels G) := min (a.clock.bar/2) ((jump a 0)/4)
def NearTarget (a : Levels G) (b : ℝ) : Prop := |b - a.clock.bar| ≤ margin a

variable {R : Recipe a} {N p : ℕ} {b : ℝ}
lemma block_positive (a : Levels G) (i): 0<Real.log (a.S.block i).val := Real.log_pos (by exact_mod_cast (show 1 < (a.S.block i).val from lt_of_lt_of_le (by decide) (a.S.block_large i)))
lemma margin_pos (g : G.Simple) : 0<margin a:= lt_min (half_pos a.clock.bar_pos) (div_pos (mul_pos (Gauge.slopeConstant_pos g) (block_positive a 0)) (by norm_num))
lemma band_insert (h : NearTarget a b) : b∈band a 0 := by
  have hx := abs_le.mp (h.trans_eq (by rfl)); have hb := a.clock.bar_pos
  simp only [band,Calendar.hatBeta,Schedule.scale_zero,mul_zero,add_zero,mem_Icc]
  dsimp only [margin] at hx; constructor <;> linarith [min_le_left (a.clock.bar/2) (jump a 0/4)]

lemma bottom_gates (h : NearTarget a b) (hd : Drifting a) {u v} (hp : R.Relays N 0 p u v) : (v.beta=floorBeta a (0+1) → u.beta ≤ b) ∧ (v.beta=ceilBeta a (0+1) → b≤u.beta) := by
  have hw:=abs_le.mp hp.drift
  have ha:= (div_le_iff₀ (block_positive a 0)).mp (hd 0)
  have hx:=abs_le.mp h; have ht := min_le_right (a.clock.bar/2) (jump a 0/4)
  unfold margin jump at hx; unfold jump at ht
  unfold floorBeta ceilBeta; simp only [Schedule.scale_succ,Schedule.scale_zero,zero_add]
  constructor <;> intro hv <;> linarith

lemma trial (h : NearTarget a b) (g:G.Simple) (hd : Drifting a) (hp : R.Issues N p) : ∃ F, Competes R p N 0 F ∧ (F 0).beta=b:= by
  have hb:=band_insert h
  classical
  rcases N with _|N
  · obtain ⟨x,hH,hx⟩:= hp.initial
    let f (m:ℕ) : Rep G (a.S.side m p) := if hm:m=0 then hm.symm ▸ x b else
      {path:= R.path 0 m, clip := (a.params m).clip,
       activities:={ reg := fun _ => ⟨0,{0},by simp⟩,forced := fun _ => ⟨{0},{0},by simp,le_rfl,fun _=>True⟩,E:=0,K:=0}, p := a.budget m, beta :=1, v:=0}
    have h₀ : f 0=x b:= dif_pos rfl
    obtain ⟨he,h₁,h₂⟩:= hx b hb
    exact ⟨f,⟨fun i hi H=> by obtain rfl:= le_antisymm H hi; rw [h₀]; exact ⟨h₁,(by rw [he]; exact hb)⟩, h₀ ▸ h₂,fun i hi H=> by omega⟩,h₀ ▸ he⟩
  let M:=N+1
  obtain ⟨l,u,he,F,hF,hC,hxL,hxR⟩:= steps p M hp g hd 1 (by omega)
  obtain ⟨T,hT,hX⟩:= hp.advances 0 (by omega) l u he (fun x=>F x 1) hC (fun x hx=> (hF x hx).prices _ le_rfl (by omega))
  have hL := (bottom_gates h hd (hX _ (left_mem_Icc.mpr he)).2).1 hxL
  have hR := (bottom_gates h hd (hX _ (right_mem_Icc.mpr he)).2).2 hxR
  obtain ⟨z,hz,hx⟩:= intermediate_value_Icc he hT.beta ⟨hL,hR⟩
  refine ⟨Function.update (F z) 0 (T z),⟨fun i h0 hi=> ?_,?_,?_⟩,by simpa only [update_self] using hx⟩
  · rcases eq_or_lt_of_le h0 with rfl|hi'; rw [update_self]; exact ⟨(hX _ hz).1,(by change (T z).beta=b at hx; rw [hx]; exact hb)⟩
    rw [update_of_ne (by omega)]; exact (hF _ hz).prices _ hi' hi
  · rw [update_of_ne (by omega)]; exact (hF _ hz).fromTop
  intro i hi h'
  rw [update_of_ne (show i+1≠0 by omega)]; rcases i with _|i
  · rw [update_self]; exact (hX _ hz).2
  rw [update_of_ne (by omega)]; exact (hF _ hz).persists _ (by omega) h'

variable {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

section
variable (hp : B.Program)
include hp

lemma advancedPath {N p} (h : NearTarget B.a b) (g : G.Simple) : ∃ F:Trail B.a p, Competes B.bake p N 0 F ∧ (F 0).beta=b ∧ ∀ m, m < N → B.Move N m p (F m) (F (m+1)) := by
    let R := { B.bake with next := fun N m p u v => B.Move N m p u v }
    have hv n m p u : Lives R n m p u ↔ Lives B.bake n m p u := by
      constructor <;> rintro ⟨A,X,C,T,Z⟩ <;> exact ⟨A,X,C,T,Z⟩
    have H : R.Issues N p := by
      constructor
      · obtain ⟨u,H,U⟩:= hp.begins N p
        exact ⟨u,H,fun t ht=> by obtain ⟨a,b,c,d,y⟩:= U t ht; exact ⟨a,(hv ..).2 b,c,d,y⟩⟩
      intro m hm l u hl Q hQ hL
      obtain ⟨x,hx,Z⟩ := hp.advances N p m hm l u hl Q hQ (fun x hx => ⟨(hv ..).1 ((hL x hx).1),(hL x hx).2⟩)
      exact ⟨x,hx,fun t ht ↦ ⟨(hv ..).2 (Z t ht).bundle, (Z t ht).ident,(B.links hm (Z t ht)).drift,Z t ht⟩⟩
    obtain ⟨T,t,hz⟩:=trial h g (Drifting.pay B.valid) H
    have he m (h:m<N): B.Move N m p (T m) (T (m+1)) := (t.persists m m.zero_le h).continues
    obtain ⟨a,b,c⟩:= t.fromTop; exact ⟨T,⟨fun i hi hx=>⟨(hv ..).1 (t.prices i hi hx).1,(t.prices i hi hx).2⟩,⟨a,b,c⟩,fun m _ hm => B.links hm (he m hm)⟩,hz,he⟩

def neighboring (b : ℝ) (H : History G) : Prop := ∃ T, H = B.bake.make T ∧
  B.bake.Stays T ∧ (∀ N p, (T N p 0).beta=b) ∧ (∀ N m p,m<N → B.Move N m p (T N p m) (T N p (m+1)))

/-- Replace reference value in Selected by explicit parameter, while keeping thresholds/hats
frozen and testing the *whole* Transfer and actual cap stack. -/
structure SelectedAt (b : ℝ) (H : History G) : Prop where
  shared N p q m : m ≤ N → (H.rep N p m).path = (H.rep N q m).path
  lawful N p m : m ≤ N → H.Conv N p m
  starts N p : (H.rep N p N).v=0 ∧ (H.rep N p N).eval = bare (H.β N p N)
  moves N p m : m < N → H.Transfer N p m
  reaches N p : H.β N p 0=b
  running : H.Running

private def fees (a:Levels G) : ℕ→ℝ
| 0 => 0
| n+1 => fees a n+(a.params (n+1)).drift

variable (g:G.Simple)
include hp g
omit hp g in
lemma pays (H : History G) (h : ∀ i j,H.β i j 0=b) (ht : ∀ i j n,n < i → H.Transfer i j n) : H.Running := by
  let a:= H.levels
  let A := H.levels.clock
  let v := |b-A.bar|
  have hd (N p i : ℕ) (hi : i≤N) : |H.β N p i-A.hatBeta i|≤fees H.levels i + v := by
    induction i with
    | zero => rw [h]; simp [Calendar.hatBeta,fees,v]
    | succ i ih =>
      calc
        _ = |(H.β N p i-A.hatBeta i)+(H.β N p (i+1)-H.β N p i-G.slopeConstant*Real.log (H.S.block i).val)| := by
          congr 1; unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold A History.S Levels.S; ring
        _ ≤ _ := (abs_add_le ..).trans ((add_le_add (ih (by omega)) ((ht N p i hi).2)).trans_eq (by change _ + _ = (fees H.levels i + _) + v; ring))
  intro ε he
  have hh : Tendsto (fun m => ((A.J (m+1):ℝ)^2)⁻¹) atTop (𝓝 0) := by
    have hz := H.levels.fits.deep.comp (tendsto_add_atTop_nat 1)
    exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp hz))
  obtain ⟨j,hj⟩ := eventually_atTop.mp (hh.eventually (ge_mem_nhds (half_pos he)))
  have hu (i : ℕ) (hi : j ≤ i) : fees a i ≤ fees a j + (ε/2)*(H.S.scale i-H.S.scale j) := by
    induction i,hi using Nat.le_induction with
    | base => rw [sub_self,mul_zero,add_zero]
    | succ i hi ih =>
      have hg : 0 < Real.log (H.S.block i).val := block_positive a i
      have hy := (div_le_iff₀ hg).mp ((a.fits.driftSmall i).trans (hj i hi))
      rw [fees,Schedule.scale_succ]; change _ ≤ _ * Real.log (H.S.block i).val at hy
      linarith
  have hb := (H.S.divergent.const_mul_atTop (half_pos he)).eventually_ge_atTop (fees a j+v)
  filter_upwards [eventually_ge_atTop j,hb] with i hi hz
  intro N p hn
  apply (hd N p i hn).trans ?_
  nlinarith only [hu i hi, mul_nonneg he.le (scale_nn a j),show fees a j+v ≤ (ε/2)*H.S.scale i from hz]

lemma all_nearby (h : NearTarget B.a b) : ∃ H : RG.History G, neighboring B b H ∧ SelectedAt b H := by
  choose f hf hβ hx using fun N p=> advancedPath (b:=b) (N:=N) (p:=p) B hp h g
  let H:=B.bake.make f
  have h₁ i j n m (hm : m ≤ i): (f i j m).path=(f i n m).path:= ((hf i j).prices m m.zero_le hm).1.path.trans (((hf i n).prices m m.zero_le hm).1.path).symm
  have h₂ i j m (hm:m ≤ i): H.Conv i j m := by obtain ⟨hh,hy⟩:=(hf i j).prices m (Nat.zero_le _) hm; exact ⟨hh.point,hh.clip,hh.valid,hy⟩
  have h₃ i j k (hk:k < i) : H.Transfer i j k := ⟨(hx i j k hk).ident,(B.links hk (hx i j k hk)).drift⟩
  exact ⟨H,⟨f,rfl,hf,hβ,fun N m p=>hx N p m⟩, h₁,h₂,fun N p=>⟨(hf N p).fromTop.scalars,(hf N p).fromTop.raw⟩,h₃,hβ,pays (b:=b) H hβ h₃⟩
end
end YM.Extension.UV
