# ==============================================================================
# Utility Functions
# ==============================================================================

#' Generate random data
#' 
#' @param n Number of observations to generate
#' @param mean Mean of the normal distribution (default: 0)
#' @param sd Standard deviation (default: 1)
#' @return A data.frame with id and value columns
generate_random_data <- function(n, mean = 0, sd = 1) {
  data.frame(
    id = seq_len(n),
    value = rnorm(n, mean = mean, sd = sd)
  )
}

#' Summary statistics
#' 
#' @param x Numeric vector
#' @return Named list with summary statistics
summary_stats <- function(x) {
  list(
    n = length(x),
    mean = mean(x, na.rm = TRUE),
    sd = sd(x, na.rm = TRUE),
    min = min(x, na.rm = TRUE),
    max = max(x, na.rm = TRUE),
    median = median(x, na.rm = TRUE)
  )
}

#' Print a formatted message
#' 
#' @param msg Message to print
#' @param prefix Optional prefix (default: ">>")
log_message <- function(msg, prefix = ">>") {
  cat(sprintf("%s %s\n", prefix, msg))
}
