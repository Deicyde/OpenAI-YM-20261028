import YM.RG08.Ducat.Cabin

/-! # Post fees must be stipulated once, here all explicit arity constants given public types.
 Compare canonical strict aggregates, may choose widths differently for different K.
-/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder Mount Tack Anchor Spar Sedan
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{O:Type}{I J:O→Type}{n m k e u r i:ℕ}(D:Exchange O)

def poem (G:Gauge)(q n:ℕ)(s:ℝ):ℝ:= if he:0<s then (Carrel.completed_held G n (stick q) he).choose else 0
lemma poem_pos (G:Gauge)(q n:ℕ)(s:ℝ):0 ≤ poem G q n s :=by
 unfold poem; split
 next H=>exact (Carrel.completed_held G n (stick q) H).choose_spec.1
 next=>exact le_rfl
lemma poem_held {F:Gird G r}{p s:ℝ}(h:Held (carpet _) s p F)(hp:0≤p)(hs:0<s): Held (carpet _) (s/(Mount.rank r:ℝ)/32) (poem G r n s*p) (completed F (stick r) n):=by
 rw [poem,dif_pos hs]; exact ((Carrel.completed_held G n (stick r) hs).choose_spec.2 F hp h).1

variable {D}{w d v:O→ℝ} (hv:∀ x:O,0<v x)(hw:∀ x:O,0<w x)(hd:∀ x:O,0≤d x)
-- autoImplicit off annotate {..}
variable {F U:O→Gird G r} -- Lance constant family need abbreviations
abbrev Gear (O:Type)(G:Gauge):O→Type:=fun _=>Tone G.ColorIndex
def Mount (D:Exchange O)(w d:O→ℝ)(F U:O→Gird G r):=Lance (I:=Gear O G) D w d F U
def Lapel (D:Exchange O)(w:O→ℝ)(F:O→Gird G r):=Bound (I:=Gear O G) D w F
abbrev Tong (O:Type)(G:Gauge):O→Type:=fun _=>Loc G 1
abbrev trail (a:ℕ)(s:O→ℝ): O→ℝ:=fun x=> s x/(RG08.Mount.rank a:ℝ)/32
include hw hd
lemma composed (h:Ducat.Mount D w d F U)(hz:D.Good (fun x=>poem G r n (w x)))(hj:0<n):
 Lance (I:=Tong O G) D (trail r w) d (fun x=> completed (F x) (stick r) n) (fun x=>completed (U x) (stick r) n):=by
 obtain ⟨a,ha,h⟩:=h; refine ⟨_,D.moreover _ _ hz ha,fun i=>?_⟩
 obtain ⟨hm,hQ,hK,hζ⟩:= h i
 refine ⟨mul_nonneg (poem_pos ..) hm,poem_held hQ hm (hw i), poem_held hK hm (hw i),?_⟩
 rw [← cracks (F i) (U i) _ (⟨0,hj⟩:Fin n) hm (hw i) hQ hK,mul_assoc];exact poem_held hζ (mul_nonneg hm (hd i)) (hw i)
lemma chaser (h:Ducat.Mount D w d F U)(hz:D.Good (fun x=>poem G r n (w x)))(hj:0<n):
 Lance (I:= Tong O G) D (trail r w) d (fun x=>RG08.Mount.flight r i (F x) e n) (fun x=>RG08.Mount.flight r i (U x) e n):=by
 by_cases he:i ≤ e ∧ e-i+RG08.Mount.rank r=n
 · simp only [RG08.Mount.flight,if_pos he];exact composed hw hd h hz hj
 simp only [RG08.Mount.flight,if_neg he];exact Ducat.zero D _ _

variable (P:O→RG.Patch)
 omit hw hd
lemma exp_price {w:O→ℝ}(h:∀ x,w x ≤ 1):D.Good fun x=>Real.exp (8*w x):=D.hale _ _ (D.steady _ (Real.exp_nonneg _)) (fun x=>Real.exp_nonneg _) (fun i=>Real.exp_le_exp.mpr (show _≤ 8 by linarith only [h i]))
lemma finer (i:O)(A:Flake n (Market (Loc G 1)))(p:ℝ)(w v:ℝ)(h:Held (carpet _) w p A)(he:0≤v)(ht:v ≤ (P i).L.val*w)(hp:0≤p): Held (carpet _) v (p*Real.exp (8*v)) (Cairn.box (P i) A):=by
 unfold Cairn.box;apply Cairn.install_held;apply (Spar.farm_cost he ht h hp)
include hv hd
lemma box {F U:O→ Flake n (Market (Loc G 1))}(h:Lance (I:=Tong O G) D w d F U)(hB:∀ i,v i ≤ (P i).L.val*w i)(hk:∀ i,v i ≤ 1): Lance (I:=fun i=>Tack.Head (P i) G) D v d (fun x=>Cairn.box (P x) (F x)) (fun x=>Cairn.box (P x) (U x)):=by
 obtain ⟨p,hp,h⟩:=h;refine ⟨_,D.moreover _ _ hp (exp_price hk),fun i=>?_⟩
 obtain ⟨hz,hM,hU,hz'⟩:=h i;refine ⟨mul_nonneg hz (Real.exp_nonneg _),finer P i _ _ _ _ hM (hv i).le (hB i) hz, finer P i _ _ _ _ hU (hv i).le (hB i) hz,?_⟩
 rw [← Cairn.box_sub,mul_right_comm];exact finer P i _ _ _ _ hz' (hv i).le (hB i) (mul_nonneg hz (hd i))

 omit hv hd
open Nacre Finset
-- cost generic demand before coating. work in packed kernel by sharper coast accounting for SAME e aperture.
variable {O:Type} {w: ℕ→ℕ→O→ℝ} {v d:O→ℝ}{D:Exchange O}
variable {A B:O→RG08.Mount.Castle G}

def Earlier (e r:ℕ)(i p:ℕ):Prop:= RG08.Mount.Live p i ∧ (i<e ∨ i=e∧r < p)
/-- earlier absolutes/cutoffs, all incl e=0 base regardless of strict charge well-foundedness. -/
def Book (D:Exchange O)(A B:O→RG08.Mount.Castle G)(w:ℕ→ℕ→O→ℝ)(d:O→ℝ)(e r:ℕ):Prop:=∀ i p, Earlier e r i p→ Mount D (w i p) d (fun x=>A x p i) (fun x=>B x p i)

-- strict term at any positive rank k>0
lemma seniors (he:∀ i p x,0<w i p x)(hd:∀ x:O,0 ≤ d x)
   (hA:Book D A B w d e r)(ha:∀ x,Fair (A x))(hb:∀ x,Fair (B x)) (hP:D.Good (fun x=>poem G m n (w i m x)))(hn:0<n)
   (hx:i ≤ e)(hforce:i=u ∧ n=RG08.Mount.rank m→ u=e → r < m) (hU:u ≤ e)(_hi:i ≤ u) : Lance (I:=Tong O G) D (trail m (w i m)) d (fun x=>RG08.Mount.flight m i (A x m i) u n) (fun x=>RG08.Mount.flight m i (B x m i) u n):=by
 by_cases ht:RG08.Mount.Live m i
 · by_cases hi: i=e ∧ u-i+RG08.Mount.rank m≠n
   · have hu {F:O→ Castle G}(x:O):RG08.Mount.flight m i (F x m i) u n=0:=by unfold RG08.Mount.flight;exact if_neg (fun h=>hi.2 h.2)
     simp_rw [hu];exact Ducat.zero D _ _
   apply chaser (he _ _) hd (hA _ _ ⟨ht,?_⟩) hP hn
   rcases lt_or_eq_of_le hx with h|rfl; exact Or.inl h
   have he:i=u:=by omega
   exact Or.inr ⟨rfl,hforce ⟨he,by specialize hi; omega⟩ he.symm⟩
 have h1 {F:O→Castle G}(h:∀ x,Fair (F x))(x):RG08.Mount.flight m i (F x m i) u n=0:=by rw [(h x).rests _ _ ht,flight_nil]
 simp_rw [h1 ha,h1 hb];exact Ducat.zero D _ _

-- coarser post candidates A B agree in not yet extracted grades. Later slot subtraction.

def Slice (_s:O→ℝ)(e:ℕ)(k:ℕ)(D:Exchange O)(w:ℕ→ℕ→O→ℝ):Prop:=∀ i q : ℕ, i ≤ e → q ≤ i→D.Good (fun x=>poem G q k (w i q x)) -- s unused
lemma pinched (hs:∀ i p x,0<w i p x)(hd:∀ x:O,0 ≤ d x)(hA:Book D A B w d e r)(ha:∀ x,Fair (A x))(hb:∀ x,Fair (B x))(hN:∀ x,overlooks (A x) e)(hM:∀ x,overlooks (B x) e)
   (hP:Slice (G:=G) v e n D w)(hn:0<n) (hz:∀ i q,i<e→q ≤ i→∀ x,v x ≤ trail q (w i q) x): Lance (I:=Tong O G) D v d (fun x=>demand (A x) e n) (fun x=>demand (B x) e n):=by
 unfold demand
 refine Lance.series _ _ _ (fun i hi=> Lance.series _ _ _ (fun q hq=>?_) hd) hd
 have hh:i ≤ e:=by simpa using hi
 have hj:q ≤ i:=by simpa using hq
 by_cases ht:i<e; swap
 · have he:i=e:=by omega
   simp_rw [he,fun x=>hN x e q le_rfl, fun x=>hM x e q le_rfl, flight_nil]
   exact Ducat.zero D _ _
 exact (seniors hs hd hA ha hb (hP _ _ hh hj) hn hh (fun h _=> by have := h.1;omega) (le_refl e) hh).vow (fun _=>le_rfl) (hz _ _ ht hj)
end YM.RG08.Ducat
